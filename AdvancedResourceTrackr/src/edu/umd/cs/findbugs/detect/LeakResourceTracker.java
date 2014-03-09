package edu.umd.cs.findbugs.detect;


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import edu.umd.cs.findbugs.ResourceCollection;
import edu.umd.cs.findbugs.SystemProperties;
import edu.umd.cs.findbugs.ba.BasicBlock;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.Edge;
import edu.umd.cs.findbugs.ba.Hierarchy;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.RepositoryLookupFailureCallback;
import edu.umd.cs.findbugs.ba.ResourceTracker;
import edu.umd.cs.findbugs.ba.ResourceValueFrame;
import edu.umd.cs.findbugs.ba.ResourceValueFrameModelingVisitor;

public class LeakResourceTracker implements ResourceTracker<Stream> {
	private ResourceCollection<Stream> resourceCollection;
	private ObjectType[] resourceObjectTypes;
	private RepositoryLookupFailureCallback lookupFailureCallback;
	static final boolean DEBUG = SystemProperties.getBoolean("fos.debug");

	static final boolean IGNORE_WRAPPED_UNINTERESTING_STREAMS = !(SystemProperties
			.getBoolean("fos.allowWUS"));
	/**
	 * Map of locations where streams are opened to the actual Stream objects.
	 */
	private Map<Location, Stream> streamOpenLocationMap;

	/**
	 * Set of all open locations and escapes of uninteresting streams.
	 */
	// private HashSet<Location> uninterestingStreamEscapeSet;
	private HashSet<Stream> uninterestingStreamEscapeSet;

	/**
	 * Set of all (potential) stream escapes.
	 */
	private TreeSet<StreamEscape> streamEscapeSet;

	/**
	 * Map of individual streams to equivalence classes. Any time a stream "A"
	 * is wrapped with a stream "B", "A" and "B" belong to the same equivalence
	 * class. If any stream in an equivalence class is closed, then we consider
	 * all of the streams in the equivalence class as having been closed.
	 */
	private Map<Stream, StreamEquivalenceClass> streamEquivalenceMap;

	public void addStreamOpenLocation(Location streamOpenLocation, Stream stream) {
		if (LeakResourceTracker.DEBUG)
			System.out.println("Stream open location at " + streamOpenLocation);
		streamOpenLocationMap.put(streamOpenLocation, stream);
		if (stream.isUninteresting())
			uninterestingStreamEscapeSet.add(stream);
	}

	/**
	 * Indicate that a stream escapes at the given target Location.
	 * 
	 * @param source
	 *            the Stream that is escaping
	 * @param target
	 *            the target Location (where the stream escapes)
	 */
	public void addStreamEscape(Stream source, Location target) {
		StreamEscape streamEscape = new StreamEscape(source, target);
		streamEscapeSet.add(streamEscape);
		if (LeakResourceTracker.DEBUG)
			System.out
					.println("Adding potential stream escape " + streamEscape);
	}

	public LeakResourceTracker(ObjectType[] resourceObjectTypes,
			RepositoryLookupFailureCallback lookupFailureCallback) {
		this.resourceObjectTypes = resourceObjectTypes;
		this.lookupFailureCallback = lookupFailureCallback;
		this.streamOpenLocationMap = new HashMap<Location, Stream>();
		this.uninterestingStreamEscapeSet = new HashSet<Stream>();
		this.streamEscapeSet = new TreeSet<StreamEscape>();
		this.streamEquivalenceMap = new HashMap<Stream, StreamEquivalenceClass>();
	}

	@Override
	public Stream isResourceCreation(BasicBlock paramBasicBlock,
			InstructionHandle paramInstructionHandle,
			ConstantPoolGen paramConstantPoolGen)
			throws DataflowAnalysisException {
		if (resourceCollection != null)
			return resourceCollection.getCreatedResource(new Location(
					paramInstructionHandle, paramBasicBlock));
		

		Instruction ins = paramInstructionHandle.getInstruction();

		if (!(ins instanceof InvokeInstruction))
			return null;

		Type returnType = ((InvokeInstruction) ins)
				.getReturnType(paramConstantPoolGen);
		
		if (!(returnType instanceof ObjectType))
			return null;

		Location location = new Location(paramInstructionHandle,
				paramBasicBlock);

		for (ObjectType resourceType : resourceObjectTypes) {
			try {
				if (Hierarchy.isSubtype((ObjectType) returnType, resourceType)) {
					return new Stream(location, resourceType.getClassName(),
							resourceType.getClassName())
							.setIgnoreImplicitExceptions(true)
							.setIsOpenOnCreation(true).setInteresting("RESOURCE_LEAK");
				}
			} catch (ClassNotFoundException e) {
				e.printStackTrace();
			}
		}

		return null;
	}

	public boolean isResourceOpen(BasicBlock basicBlock,
			InstructionHandle handle, ConstantPoolGen cpg, Stream resource,
			ResourceValueFrame frame) {
		return resource.isStreamOpen(basicBlock, handle, cpg, frame);
	}

	@Override
	public boolean isResourceClose(BasicBlock paramBasicBlock,
			InstructionHandle paramInstructionHandle,
			ConstantPoolGen paramConstantPoolGen, Stream paramResource,
			ResourceValueFrame paramResourceValueFrame)
			throws DataflowAnalysisException {
		return paramResource.isStreamClose(paramBasicBlock,
				paramInstructionHandle, paramConstantPoolGen,
				paramResourceValueFrame, lookupFailureCallback);
	}

	@Override
	public boolean mightCloseResource(BasicBlock paramBasicBlock,
			InstructionHandle paramInstructionHandle,
			ConstantPoolGen paramConstantPoolGen)
			throws DataflowAnalysisException {
		return Stream.mightCloseStream(paramBasicBlock, paramInstructionHandle,
				paramConstantPoolGen);
	}

	@Override
	public ResourceValueFrameModelingVisitor createVisitor(
			Stream paramResource, ConstantPoolGen paramConstantPoolGen) {
		return new ResourceLeavModelingVisitor(paramConstantPoolGen, this,
				paramResource);
	}

	@Override
	public boolean ignoreImplicitExceptions(Stream paramResource) {
		return paramResource.ignoreImplicitExceptions();
	}

	@Override
	public boolean ignoreExceptionEdge(Edge paramEdge, Stream paramResource,
			ConstantPoolGen paramConstantPoolGen) {
		return false;
	}

	@Override
	public boolean isParamInstance(Stream paramResource, int paramInt) {
		return paramResource.getInstanceParam() == paramInt;
	}

	/**
	 * Set the precomputed ResourceCollection for the method.
	 */
	public void setResourceCollection(
			ResourceCollection<Stream> resourceCollection) {
		this.resourceCollection = resourceCollection;
	}

	/**
	 * Transitively mark all streams into which uninteresting streams (such as
	 * System.out) escape. This handles the rule that wrapping an uninteresting
	 * stream makes the wrapper uninteresting as well.
	 */
	public void markTransitiveUninterestingStreamEscapes() {
		// Eliminate all stream escapes where the target isn't really
		// a stream open location point.
		for (Iterator<StreamEscape> i = streamEscapeSet.iterator(); i.hasNext();) {
			StreamEscape streamEscape = i.next();
			if (!isStreamOpenLocation(streamEscape.target)) {
				if (LeakResourceTracker.DEBUG)
					System.out.println("Eliminating false stream escape "
							+ streamEscape);
				i.remove();
			}
		}

		// Build initial stream equivalence classes.
		// Each stream starts out in its own separate
		// equivalence class.
		for (Iterator<Stream> i = resourceCollection.resourceIterator(); i
				.hasNext();) {
			Stream stream = i.next();
			StreamEquivalenceClass equivalenceClass = new StreamEquivalenceClass();
			equivalenceClass.addMember(stream);
			streamEquivalenceMap.put(stream, equivalenceClass);
		}

		// Starting with the set of uninteresting stream open location points,
		// propagate all uninteresting stream escapes. Iterate until there
		// is no change. This also builds the map of stream equivalence classes.
		Set<Stream> orig = new HashSet<Stream>();
		do {
			orig.clear();
			orig.addAll(uninterestingStreamEscapeSet);

			for (StreamEscape streamEscape : streamEscapeSet) {
				if (isUninterestingStreamEscape(streamEscape.source)) {
					if (LeakResourceTracker.DEBUG)
						System.out.println("Propagating stream escape "
								+ streamEscape);
					Stream target = streamOpenLocationMap
							.get(streamEscape.target);
					if (target == null)
						throw new IllegalStateException();
					uninterestingStreamEscapeSet.add(target);

					// Combine equivalence classes for source and target
					StreamEquivalenceClass sourceClass = streamEquivalenceMap
							.get(streamEscape.source);
					StreamEquivalenceClass targetClass = streamEquivalenceMap
							.get(target);
					if (sourceClass != targetClass) {
						sourceClass.addAll(targetClass);
						for (Iterator<Stream> j = targetClass.memberIterator(); j
								.hasNext();) {
							Stream stream = j.next();
							streamEquivalenceMap.put(stream, sourceClass);
						}
					}
				}
			}
		} while (!orig.equals(uninterestingStreamEscapeSet));
	}

	/**
	 * Determine if given Location is a stream open location point.
	 * 
	 * @param location
	 *            the Location
	 */
	private boolean isStreamOpenLocation(Location location) {
		return streamOpenLocationMap.get(location) != null;
	}

	/**
	 * Determine if an uninteresting stream escapes at given location.
	 * markTransitiveUninterestingStreamEscapes() should be called first.
	 * 
	 * @param stream
	 *            the stream
	 * @return true if an uninteresting stream escapes at the location
	 */
	public boolean isUninterestingStreamEscape(Stream stream) {
		return uninterestingStreamEscapeSet.contains(stream);
	}

	/**
	 * Get the equivalence class for given stream. May only be called if
	 * markTransitiveUninterestingStreamEscapes() has been called.
	 * 
	 * @param stream
	 *            the stream
	 * @return the set containing the equivalence class for the given stream
	 */
	public StreamEquivalenceClass getStreamEquivalenceClass(Stream stream) {
		return streamEquivalenceMap.get(stream);
	}
}
