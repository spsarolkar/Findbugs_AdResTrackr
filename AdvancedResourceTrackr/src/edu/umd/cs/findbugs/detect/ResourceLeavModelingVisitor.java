package edu.umd.cs.findbugs.detect;


import org.apache.bcel.Constants;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;

import edu.umd.cs.findbugs.ba.BasicBlock;
import edu.umd.cs.findbugs.ba.DataflowAnalysisException;
import edu.umd.cs.findbugs.ba.Location;
import edu.umd.cs.findbugs.ba.ResourceValue;
import edu.umd.cs.findbugs.ba.ResourceValueFrame;
import edu.umd.cs.findbugs.ba.ResourceValueFrameModelingVisitor;

public class ResourceLeavModelingVisitor extends
		ResourceValueFrameModelingVisitor {
	private LeakResourceTracker resourceTracker;

	private Stream stream;

	private Location location;

	public ResourceLeavModelingVisitor(ConstantPoolGen cpg,
			LeakResourceTracker resourceTracker, Stream stream) {
		super(cpg);
		this.resourceTracker = resourceTracker;
		this.stream = stream;
	}

	@Override
	public void transferInstruction(InstructionHandle handle,
			BasicBlock basicBlock) throws DataflowAnalysisException {
		// Record what Location we are analyzing
		this.location = new Location(handle, basicBlock);

		final Instruction ins = handle.getInstruction();
		final ResourceValueFrame frame = getFrame();

		int status = -1;
		boolean created = false;

		// Is a resource created, opened, or closed by this instruction?
		Location creationPoint = stream.getLocation();
		if (handle == creationPoint.getHandle()
				&& basicBlock == creationPoint.getBasicBlock()) {
			// Resource creation
			if (stream.isOpenOnCreation()) {
				status = ResourceValueFrame.OPEN;
				stream.setOpenLocation(location);
				resourceTracker.addStreamOpenLocation(location, stream);
			} else {
				status = ResourceValueFrame.CREATED;
			}
			created = true;
		} else if (resourceTracker.isResourceOpen(basicBlock, handle, cpg,
				stream, frame)) {
			// Resource opened
			status = ResourceValueFrame.OPEN;
			stream.setOpenLocation(location);
			resourceTracker.addStreamOpenLocation(location, stream);
		} else if (resourceTracker.isResourceClose(basicBlock, handle, cpg,
				stream, frame)) {
			// Resource closed
			status = ResourceValueFrame.CLOSED;
		}

		// Model use of instance values in frame slots
		analyzeInstruction(ins);

		// If needed, update frame status
		if (status != -1) {
			frame.setStatus(status);
			if (created)
				frame.setValue(frame.getNumSlots() - 1,
						ResourceValue.instance());
		}

	}

	@Override
	protected boolean instanceEscapes(InvokeInstruction inv, int instanceArgNum) {
		ConstantPoolGen cpg = getCPG();
		String className = inv.getClassName(cpg);

		// System.out.print("[Passed as arg="+instanceArgNum+" at " + inv +
		// "]");

		boolean escapes = (inv.getOpcode() == Constants.INVOKESTATIC || instanceArgNum != 0);
		String methodName = inv.getMethodName(cpg);
		String methodSig = inv.getSignature(cpg);
		if (inv.getOpcode() == Constants.INVOKEVIRTUAL
				&& (methodName.equals("load")
						|| methodName.equals("loadFromXml")
						|| methodName.equals("store") || methodName
							.equals("save"))
				&& className.equals("java.util.Properties"))
			escapes = false;
		if (inv.getOpcode() == Constants.INVOKEVIRTUAL
				&& (methodName.equals("load") || methodName.equals("store"))
				&& className.equals("java.security.KeyStore"))
			escapes = false;
		if (inv.getOpcode() == Constants.INVOKEVIRTUAL
				&& "getChannel".equals(methodName)
				&& "()Ljava/nio/channels/FileChannel;".equals(methodSig))
			escapes = true;

		if (ResourceLeakDetector.DEBUG && escapes) {
			System.out.println("ESCAPE at " + location + " at call to "
					+ className + "." + methodName + ":" + methodSig);
		}

		// Record the fact that this might be a stream escape
		if (stream.getOpenLocation() != null)
			resourceTracker.addStreamEscape(stream, location);

		return escapes;
	}
}
