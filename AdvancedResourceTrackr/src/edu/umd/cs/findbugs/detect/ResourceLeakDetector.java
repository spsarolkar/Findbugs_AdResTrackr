package edu.umd.cs.findbugs.detect;


import java.util.BitSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import edu.umd.cs.findbugs.BugInstance;
import edu.umd.cs.findbugs.BugReporter;
import edu.umd.cs.findbugs.ResourceCollection;
import edu.umd.cs.findbugs.ResourceTrackingDetector;
import edu.umd.cs.findbugs.SourceLineAnnotation;
import edu.umd.cs.findbugs.StatelessDetector;
import edu.umd.cs.findbugs.SystemProperties;
import edu.umd.cs.findbugs.TypeAnnotation;
import edu.umd.cs.findbugs.ba.CFG;
import edu.umd.cs.findbugs.ba.CFGBuilderException;
import edu.umd.cs.findbugs.ba.ClassContext;
import edu.umd.cs.findbugs.ba.Dataflow;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.Hierarchy;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.ObjectTypeFactory;
import edu.umd.cs.findbugs.ba.ResourceValueAnalysis;
import edu.umd.cs.findbugs.ba.ResourceValueFrame;

/**
 * This Detector to looks for resource(stream or jdbc object) that is
 * initialized in separate method and not closed This is in addition to check
 * made by FindOpenStream detector which takes care of jdbc resource/stream
 * created using some well defined factory methods, Problem with FindOpenStream
 * is that any method other than factory method creating the resource and
 * returning remain undetected
 * 
 * @author Sunil Sarolkar
 */
public class ResourceLeakDetector extends
		ResourceTrackingDetector<Stream, LeakResourceTracker> implements
		StatelessDetector {
	static final boolean DEBUG = SystemProperties.getBoolean("fos.debug");
	static final boolean IGNORE_WRAPPED_UNINTERESTING_STREAMS = !SystemProperties
			.getBoolean("fos.allowWUS");
	static final ObjectType[] streamBaseList = {
			ObjectTypeFactory.getInstance("java.io.InputStream"),
			ObjectTypeFactory.getInstance("java.io.OutputStream"),
			ObjectTypeFactory.getInstance("java.util.zip.ZipFile"),
			ObjectTypeFactory.getInstance("java.io.Reader"),
			ObjectTypeFactory.getInstance("java.io.Writer"),
			ObjectTypeFactory.getInstance("java.sql.Connection"),
			ObjectTypeFactory.getInstance("java.sql.Statement"),
			ObjectTypeFactory.getInstance("java.sql.ResultSet") };

	// List of words that must appear in names of classes which
	// create possible resources to be tracked. If we don't see a
	// class containing one of these words, then we don't run the
	// detector on the class.
	private static final String[] PRESCREEN_CLASS_LIST = { "Stream", "Reader",
			"Writer", "ZipFile", "JarFile", "DriverManager", "Connection",
			"Statement" };

	/*
	 * ----------------------------------------------------------------------
	 * Helper classes
	 * ----------------------------------------------------------------------
	 */

	private static class PotentialOpenStream {
		public final String bugType;

		public final int priority;

		public final Stream stream;

		@Override
		public String toString() {
			return stream.toString();
		}

		public PotentialOpenStream(String bugType, int priority, Stream stream) {
			this.bugType = bugType;
			this.priority = priority;
			this.stream = stream;
		}
	}

	private List<PotentialOpenStream> potentialOpenStreamList;

	public ResourceLeakDetector(BugReporter bugReporter) {
		super(bugReporter);
		this.potentialOpenStreamList = new LinkedList<PotentialOpenStream>();
	}

	@Override
	public LeakResourceTracker getResourceTracker(ClassContext arg0, Method arg1)
			throws DataflowAnalysisException, CFGBuilderException {
		return new LeakResourceTracker(streamBaseList, bugReporter);
	}

	 @Override
	    public void visitClassContext(ClassContext classContext) {
	        JavaClass jclass = classContext.getJavaClass();

	        // Check to see if the class references any other classes
	        // which could be resources we want to track.
	        // If we don't find any such classes, we skip analyzing
	        // the class. (Note: could do this by method.)
	        boolean sawResourceClass = false;
	        for (int i = 0; i < jclass.getConstantPool().getLength(); ++i) {
	            Constant constant = jclass.getConstantPool().getConstant(i);
	            String className = null;
	            if (constant instanceof ConstantMethodref) {
	                ConstantMethodref cmr = (ConstantMethodref) constant;

	                int classIndex = cmr.getClassIndex();
	                className = jclass.getConstantPool().getConstantString(classIndex, Constants.CONSTANT_Class);
	            } else if (constant instanceof ConstantInterfaceMethodref) {
	                ConstantInterfaceMethodref cmr = (ConstantInterfaceMethodref) constant;

	                int classIndex = cmr.getClassIndex();
	                className = jclass.getConstantPool().getConstantString(classIndex, Constants.CONSTANT_Class);
	            }

	            if (className != null) {
	                if (DEBUG)
	                    System.out.println("FindOpenStream: saw class " + className);

	                for (String aPRESCREEN_CLASS_LIST : PRESCREEN_CLASS_LIST) {
	                    if (className.indexOf(aPRESCREEN_CLASS_LIST) >= 0) {
	                        sawResourceClass = true;
	                        break;
	                    }
	                }
	            }

	        }

	        if (sawResourceClass) {
	            super.visitClassContext(classContext);
	        }
	    }
	 
	@Override
	public void inspectResult(
			ClassContext arg0,
			MethodGen arg1,
			CFG cfg,
			Dataflow<ResourceValueFrame, ResourceValueAnalysis<Stream>> dataflow,
			Stream stream) {
		ResourceValueFrame exitFrame = dataflow.getResultFact(cfg.getExit());

		int exitStatus = exitFrame.getStatus();
		if (exitStatus == ResourceValueFrame.OPEN
				|| exitStatus == ResourceValueFrame.OPEN_ON_EXCEPTION_PATH) {

			// FIXME: Stream object should be queried for the
			// priority.

			String bugType = stream.getBugType();
			int priority = NORMAL_PRIORITY;
			if (exitStatus == ResourceValueFrame.OPEN_ON_EXCEPTION_PATH) {
				bugType += "_EXCEPTION_PATH";
				priority = LOW_PRIORITY;
			}

			potentialOpenStreamList.add(new PotentialOpenStream(bugType,
					priority, stream));
		} else if (exitStatus == ResourceValueFrame.CLOSED) {
			// Remember that this stream was closed on all paths.
			// Later, we will mark all of the streams in its equivalence class
			// as having been closed.
			stream.setClosed();
		}

	}

	@Override
	public boolean prescreen(ClassContext classContext, Method method,
			boolean mightClose) {
		BitSet bytecodeSet = classContext.getBytecodeSet(method);
		if (bytecodeSet == null)
			return false;
		return bytecodeSet.get(Constants.NEW)
				|| bytecodeSet.get(Constants.INVOKEINTERFACE)
				|| bytecodeSet.get(Constants.INVOKESPECIAL)
				|| bytecodeSet.get(Constants.INVOKESTATIC)
				|| bytecodeSet.get(Constants.INVOKEVIRTUAL);
	}

	@Override
	public Object clone() {
		try {
			return super.clone();
		} catch (CloneNotSupportedException e) {
			throw new AssertionError(e);
		}
	}

	@Override
	public void analyzeMethod(ClassContext classContext, Method method,
			LeakResourceTracker resourceTracker,
			ResourceCollection<Stream> resourceCollection)
			throws CFGBuilderException, DataflowAnalysisException {

		potentialOpenStreamList.clear();

		JavaClass javaClass = classContext.getJavaClass();
		MethodGen methodGen = classContext.getMethodGen(method);
		if (methodGen == null)
			return;
		CFG cfg = classContext.getCFG(method);

		// Add Streams passed into the method as parameters.
		// These are uninteresting, and should poison
		// any streams which wrap them.
		try {
			Type[] parameterTypeList = Type.getArgumentTypes(methodGen
					.getSignature());
			Location firstLocation = new Location(cfg.getEntry()
					.getFirstInstruction(), cfg.getEntry());

			int local = methodGen.isStatic() ? 0 : 1;

			for (Type type : parameterTypeList) {
				if (type instanceof ObjectType) {
					ObjectType objectType = (ObjectType) type;

					for (ObjectType streamBase : streamBaseList) {
						if (Hierarchy.isSubtype(objectType, streamBase)) {
							// OK, found a parameter that is a resource.
							// Create a Stream object to represent it.
							// The Stream will be uninteresting, so it will
							// inhibit reporting for any stream that wraps it.
							Stream paramStream = new Stream(firstLocation,
									objectType.getClassName(),
									streamBase.getClassName());
							paramStream.setIsOpenOnCreation(true);
							paramStream.setOpenLocation(firstLocation);
							paramStream.setInstanceParam(local);
							resourceCollection
									.addPreexistingResource(paramStream);

							break;
						}
					}
				}

				switch (type.getType()) {
				case Constants.T_LONG:
				case Constants.T_DOUBLE:
					local += 2;
					break;
				default:
					local += 1;
					break;
				}
			}
		} catch (ClassNotFoundException e) {
			bugReporter.reportMissingClass(e);
		}

		// Set precomputed map of Locations to Stream creation points.
		// That way, the StreamResourceTracker won't have to
		// repeatedly try to figure out where Streams are created.
		resourceTracker.setResourceCollection(resourceCollection);

		super.analyzeMethod(classContext, method, resourceTracker,
				resourceCollection);

		// Compute streams that escape into other streams:
		// this takes wrapper streams into account.
		// This will also compute equivalence classes of streams,
		// so that if one stream in a class is closed,
		// they are all considered closed.
		// (FIXME: this is too simplistic, especially if buffering
		// is involved. Sometime we should really think harder
		// about how this should work.)
		resourceTracker.markTransitiveUninterestingStreamEscapes();

		// For each stream closed on all paths, mark its equivalence
		// class as being closed.
		for (Iterator<Stream> i = resourceCollection.resourceIterator(); i
				.hasNext();) {
			Stream stream = i.next();
			StreamEquivalenceClass equivalenceClass = resourceTracker
					.getStreamEquivalenceClass(stream);
			if (stream.isClosed())
				equivalenceClass.setClosed();
		}

		// Iterate through potential open streams, reporting warnings
		// for the "interesting" streams that haven't been closed
		// (and aren't in an equivalence class with another stream
		// that was closed).
		for (PotentialOpenStream pos : potentialOpenStreamList) {
			Stream stream = pos.stream;
			if (stream.isClosed())
			{
				continue;
			}

			if (stream.isUninteresting()){
				continue;
			}

			Location openLocation = stream.getOpenLocation();
			
			if (openLocation == null){
				continue;
			}

			if (IGNORE_WRAPPED_UNINTERESTING_STREAMS
					&& resourceTracker.isUninterestingStreamEscape(stream)){
				continue;
			}

			String sourceFile = javaClass.getSourceFileName();
			String leakClass = stream.getStreamBase();
			if (isMainMethod(method)
					&& (leakClass.contains("InputStream") || leakClass
							.contains("Reader"))){
				return;
			}
			bugAccumulator.accumulateBug(
					new BugInstance(this, pos.bugType, pos.priority)
							.addClassAndMethod(methodGen, sourceFile)
							.addTypeOfNamedClass(leakClass)
							.describe(TypeAnnotation.CLOSEIT_ROLE),
					SourceLineAnnotation.fromVisitedInstruction(classContext,
							methodGen, sourceFile, stream.getLocation()
									.getHandle()));
		}
	}

	public static boolean isMainMethod(Method method) {
		return method.isStatic() && method.getName().equals("main")
				&& method.getSignature().equals("([Ljava/lang/String;)V");
	}

}
