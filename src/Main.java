import java.io.File;
import java.io.IOException;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.jf.dexlib2.AccessFlags;
import org.jf.dexlib2.DexFileFactory;
import org.jf.dexlib2.Format;
import org.jf.dexlib2.Opcode;
import org.jf.dexlib2.Opcodes;
import org.jf.dexlib2.ReferenceType;
import org.jf.dexlib2.dexbacked.DexBackedDexFile;
import org.jf.dexlib2.dexbacked.DexBackedTypedExceptionHandler;
import org.jf.dexlib2.dexbacked.instruction.*;
import org.jf.dexlib2.iface.Annotation;
import org.jf.dexlib2.iface.ClassDef;
import org.jf.dexlib2.iface.DexFile;
import org.jf.dexlib2.iface.ExceptionHandler;
import org.jf.dexlib2.iface.Field;
import org.jf.dexlib2.iface.Method;
import org.jf.dexlib2.iface.MethodImplementation;
import org.jf.dexlib2.iface.MethodParameter;
import org.jf.dexlib2.iface.TryBlock;
import org.jf.dexlib2.iface.instruction.Instruction;
import org.jf.dexlib2.iface.instruction.formats.*;
import org.jf.dexlib2.iface.reference.Reference;
import org.jf.dexlib2.iface.instruction.TwoRegisterInstruction;
import org.jf.dexlib2.immutable.ImmutableClassDef;
import org.jf.dexlib2.immutable.ImmutableDexFile;
import org.jf.dexlib2.immutable.ImmutableExceptionHandler;
import org.jf.dexlib2.immutable.ImmutableMethod;
import org.jf.dexlib2.immutable.ImmutableMethodImplementation;
import org.jf.dexlib2.immutable.ImmutableMethodParameter;
import org.jf.dexlib2.immutable.ImmutableTryBlock;
import org.jf.dexlib2.immutable.instruction.*;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction10t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction10x;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction11n;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction11x;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction20t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction21c;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction21t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction22t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction30t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction31t;
import org.jf.dexlib2.immutable.instruction.ImmutableInstruction35c;
import org.jf.dexlib2.immutable.reference.ImmutableFieldReference;
import org.jf.dexlib2.immutable.reference.ImmutableMethodReference;
import org.jf.dexlib2.immutable.reference.ImmutableStringReference;
import org.jf.dexlib2.immutable.reference.ImmutableTypeReference;
import org.jf.dexlib2.rewriter.DexRewriter;
import org.jf.dexlib2.rewriter.Rewriter;
import org.jf.dexlib2.rewriter.RewriterModule;
import org.jf.dexlib2.util.ReferenceUtil;


public class Main {
	static List<Method> encodedBlocks = new LinkedList<Method>();
	static int API = 21; //api level
	static Set<Field> privateFields = new HashSet<Field>();
	static Set<Method> privateMethods = new HashSet<Method>();
	static List<Instruction> SDCB = new LinkedList<Instruction>();;
	public static void main(String[] arguments) {
		File f = new File("assets/classes.dex");
		try {
		DexFile d = DexFileFactory.loadDexFile(f, Opcodes.forApi(API));
		List<ClassDef> classes = new LinkedList<ClassDef>();
		for (ClassDef c : d.getClasses()) {
			if (c.getSuperclass().toString() == null || !c.getSuperclass().equals("Landroid/support/v7/app/AppCompatActivity;")) {
				//System.out.println(c.getSuperclass().toString()+": Not Application");
				classes.add(c);
				
			} else {
			List<Method> dmethods = new LinkedList<Method>();
			List<Method> vmethods = new LinkedList<Method>();
			for(Method m : c.getDirectMethods()) {
				dmethods.add(adjustedMethod(c, m));
			}
			for(Method m : c.getVirtualMethods()) {
				vmethods.add(adjustedMethod(c, m));
			}
			classes.add(new ImmutableClassDef(c.getType(), c.getAccessFlags(), c.getSuperclass(), c.getInterfaces(), 
					c.getSourceFile(), c.getAnnotations(), c.getStaticFields(), c.getInstanceFields(), dmethods, vmethods));
			}
		}
		DexFileFactory.writeDexFile("out/Output.dex", new ImmutableDexFile(Opcodes.forApi(API), classes));
		classes.clear();
		classes.add(new ImmutableClassDef("LSDC/ImportClass;", 1, "Ljava/lang/Object;", null, "ImportClass.java", null, null, null, encodedBlocks, null));
		DexFileFactory.writeDexFile("out/ImportClass.dex", new ImmutableDexFile(Opcodes.forApi(API), classes));
		} catch (IOException e) {
			System.out.println("IOException");
		}
	}
	
	
	static private LinkedList<codeBlock> getSDCBlocks(Method method) {
		LinkedList<codeBlock> result = new LinkedList<codeBlock>();
		int instructionsize = 0;
		codeBlock current = null;
		String returnType = null;
		String[] registerClasses = new String[method.getImplementation().getRegisterCount()];
		String[] constants = new String[method.getImplementation().getRegisterCount()];
		List<tInstruction> jumps = getTInstructions(method);
		int indexPointer = 0;
		if ((8 & method.getAccessFlags()) == 0) {
			registerClasses[(method.getImplementation().getRegisterCount()-method.getParameters().size())-1] = method.getDefiningClass();
		}
		for(int i = 0; i< method.getParameters().size(); i++) {
			registerClasses[(method.getImplementation().getRegisterCount()-method.getParameters().size())+i] = (String) method.getParameterTypes().get(i);
		}
		if(method.getName().equals("method")) {
			System.out.println(method.getDefiningClass() + " " + method.getName() + " " +method.getImplementation().getRegisterCount()+ " " + method.getParameters().size());
			for(String s : registerClasses) {
				System.out.println(s);
			}
		}
		for (Instruction in : method.getImplementation().getInstructions()) {
			if(current != null) {
				if(current.end == indexPointer) {
					for(int i = 0; i < method.getImplementation().getRegisterCount(); i++) {
						current.endClasses[i] = registerClasses[i];
					}
					result.add(current);
					current = null;
				} else {
					current.instructions.add(in);
				}
				
			}
			switch(in.getOpcode().format) {
			case Format10t :
				break;
			case Format10x :
				break;
			case Format11n :
				Instruction11n inst11n = (Instruction11n) in;
				registerClasses[inst11n.getRegisterA()] = getTypeFromName(Integer.class.getName());
				if (current != null) {
					current.registersActive[inst11n.getRegisterA()] = true;
				}
				break;
			case Format11x :
				Instruction11x inst11x = (Instruction11x) in;
				if (in.getOpcode().equals(Opcode.MOVE_RESULT) || in.getOpcode().equals(Opcode.MOVE_RESULT_OBJECT)) {
				registerClasses[inst11x.getRegisterA()] = returnType;
				} else if (in.getOpcode().equals(Opcode.MOVE_RESULT_WIDE)) {
					registerClasses[inst11x.getRegisterA()] = returnType;
					registerClasses[inst11x.getRegisterA()+1] = returnType;
				}
				if (current != null) {
					current.registersActive[inst11x.getRegisterA()] = true;
					if (in.getOpcode().equals(Opcode.MOVE_RESULT_WIDE)) {
						current.registersActive[inst11x.getRegisterA()+1] = true;
					}
				}
				break;
			case Format12x :
				Instruction12x inst12x = (Instruction12x) in;
				if (in.getOpcode().equals(Opcode.MOVE) || in.getOpcode().equals(Opcode.MOVE_WIDE) || in.getOpcode().equals(Opcode.MOVE_OBJECT)) {
					registerClasses[inst12x.getRegisterA()] = registerClasses[inst12x.getRegisterB()];
					//registerClasses[inst12x.getRegisterB()] = null; ##Does move leave source register in peace? probably.
				} else if(in.getOpcode().equals(Opcode.ARRAY_LENGTH) || in.getOpcode().equals(Opcode.NEG_INT) || in.getOpcode().equals(Opcode.NOT_INT)
						|| in.getOpcode().equals(Opcode.LONG_TO_INT) || in.getOpcode().equals(Opcode.FLOAT_TO_INT) || in.getOpcode().equals(Opcode.ADD_INT_2ADDR)
						|| in.getOpcode().equals(Opcode.SUB_INT_2ADDR) || in.getOpcode().equals(Opcode.MUL_INT_2ADDR) || in.getOpcode().equals(Opcode.REM_INT_2ADDR)
						|| in.getOpcode().equals(Opcode.DIV_INT_2ADDR) || in.getOpcode().equals(Opcode.AND_INT_2ADDR) || in.getOpcode().equals(Opcode.OR_INT_2ADDR)
						|| in.getOpcode().equals(Opcode.XOR_INT_2ADDR) || in.getOpcode().equals(Opcode.SHL_INT_2ADDR)
						|| in.getOpcode().equals(Opcode.SHR_INT_2ADDR) || in.getOpcode().equals(Opcode.USHR_INT_2ADDR)) {
					registerClasses[inst12x.getRegisterA()] = "I";
				} else if(in.getOpcode().equals(Opcode.NEG_LONG) || in.getOpcode().equals(Opcode.NOT_LONG) || in.getOpcode().equals(Opcode.INT_TO_LONG)
						|| in.getOpcode().equals(Opcode.FLOAT_TO_LONG) || in.getOpcode().equals(Opcode.DOUBLE_TO_LONG) || in.getOpcode().equals(Opcode.ADD_LONG_2ADDR)
						|| in.getOpcode().equals(Opcode.SUB_LONG_2ADDR) || in.getOpcode().equals(Opcode.MUL_LONG_2ADDR) || in.getOpcode().equals(Opcode.DIV_LONG_2ADDR)
						|| in.getOpcode().equals(Opcode.REM_LONG_2ADDR) || in.getOpcode().equals(Opcode.AND_LONG_2ADDR) || in.getOpcode().equals(Opcode.OR_LONG_2ADDR)
						|| in.getOpcode().equals(Opcode.XOR_LONG_2ADDR) || in.getOpcode().equals(Opcode.SHL_LONG_2ADDR)
						|| in.getOpcode().equals(Opcode.SHR_LONG_2ADDR) || in.getOpcode().equals(Opcode.USHR_LONG_2ADDR)) {
					registerClasses[inst12x.getRegisterA()] = "J";
				} else if(in.getOpcode().equals(Opcode.NEG_FLOAT) || in.getOpcode().equals(Opcode.INT_TO_FLOAT) || in.getOpcode().equals(Opcode.LONG_TO_FLOAT)
						|| in.getOpcode().equals(Opcode.DOUBLE_TO_FLOAT) || in.getOpcode().equals(Opcode.ADD_FLOAT_2ADDR) || in.getOpcode().equals(Opcode.SUB_FLOAT_2ADDR)
						|| in.getOpcode().equals(Opcode.MUL_FLOAT_2ADDR) || in.getOpcode().equals(Opcode.DIV_FLOAT_2ADDR) || in.getOpcode().equals(Opcode.REM_FLOAT_2ADDR)) {
					registerClasses[inst12x.getRegisterA()] = "F";
				} else {
					registerClasses[inst12x.getRegisterA()] = "D";
				}
				break;
			case Format20bc :
				Instruction20bc inst20bc = (Instruction20bc) in;
				//TODO: potentially handling reference? 20bc might be useless
				break;
			case Format20t :
				Instruction20t inst20t = (Instruction20t) in;
				break;
			case Format21c :
				Instruction21c inst21c = (Instruction21c) in;
				if(current != null) {
					current.registersActive[inst21c.getRegisterA()] = true;
				}
				if(in.getOpcode().equals(Opcode.CHECK_CAST) || in.getOpcode().equals(Opcode.CONST_CLASS) || in.getOpcode().equals(Opcode.NEW_INSTANCE)) {
					registerClasses[inst21c.getRegisterA()] = inst21c.getReference().toString();
				}else if(in.getOpcode().equals(Opcode.CONST_STRING)) {
					registerClasses[inst21c.getRegisterA()] = getTypeFromName(String.class.getTypeName());
					constants[inst21c.getRegisterA()] = inst21c.getReference().toString();
				} else if(in.getOpcode().equals(Opcode.SGET) || in.getOpcode().equals(Opcode.SGET_WIDE) || in.getOpcode().equals(Opcode.SGET_OBJECT)
						|| in.getOpcode().equals(Opcode.SGET_BOOLEAN) || in.getOpcode().equals(Opcode.SGET_BYTE)
						|| in.getOpcode().equals(Opcode.SGET_CHAR) || in.getOpcode().equals(Opcode.SGET_SHORT)) {
					registerClasses[inst21c.getRegisterA()] = inst21c.getReference().toString().substring(inst21c.getReference().toString().lastIndexOf("->TYPE:")+7);
				}
				break;
			case Format21ih :
				Instruction21ih inst21ih = (Instruction21ih) in;
				//no 21ih opcodes? probably const/high16
				registerClasses[inst21ih.getRegisterA()] = "I";
				break;
			case Format21lh :
				Instruction21lh inst21lh = (Instruction21lh) in;
				registerClasses[inst21lh.getRegisterA()] = "D";
				//Used Double instead of Int since it's a double-register value
				break;
			case Format21s :
				Instruction21s inst21s = (Instruction21s) in;
				if(in.getOpcode().equals(Opcode.CONST_16)) {
				registerClasses[inst21s.getRegisterA()] = "I";
				} else {
				registerClasses[inst21s.getRegisterA()] = "D";
				}
				break;
			case Format21t :
				Instruction21t inst21t = (Instruction21t) in;
					if (in.getOpcode().equals(Opcode.IF_NEZ)){
						current = new codeBlock(indexPointer, indexPointer + inst21t.getCodeOffset(), "0", method.getImplementation().getRegisterCount());
						for (int i = 0; i < method.getImplementation().getRegisterCount(); i++) {
							current.startClasses[i] = registerClasses[i];
						}
					}
				break;
			case Format22b :
				Instruction22b inst22b = (Instruction22b) in;
				registerClasses[inst22b.getRegisterA()] = "I";
				break;
			case Format22c :
				Instruction22c inst22c = (Instruction22c) in;
				if (in.getOpcode().equals(Opcode.INSTANCE_OF)) {
					registerClasses[inst22c.getRegisterA()] = "Z";
				} else if(in.getOpcode().equals(Opcode.NEW_ARRAY)) {
					registerClasses[inst22c.getRegisterA()] = inst22c.getReference().toString();
				} else if(in.getOpcode().equals(Opcode.IGET) || in.getOpcode().equals(Opcode.IGET_WIDE) || in.getOpcode().equals(Opcode.IGET_OBJECT)
						|| in.getOpcode().equals(Opcode.IGET_BOOLEAN) || in.getOpcode().equals(Opcode.IGET_BYTE)
						|| in.getOpcode().equals(Opcode.IGET_CHAR) || in.getOpcode().equals(Opcode.IGET_SHORT)
						) {
					//TODO: Maybe quick/volatile get instructions? Might not occur...
					registerClasses[inst22c.getRegisterA()] = "L"+inst22c.getReference().toString().substring(inst22c.getReference().toString().lastIndexOf(":") +2);
				}
				break;
			case Format22cs :
				//No 22cs operations?
				break;
			case Format22s :
				Instruction22s inst22s = (Instruction22s) in;
				registerClasses[inst22s.getRegisterA()] = "I";
				break;
			case Format22t :
				Instruction22t inst22t = (Instruction22t) in;
				if(in.getOpcode().equals(Opcode.IF_NE) && constants[inst22t.getRegisterB()] != null) {
					current = new codeBlock(indexPointer, indexPointer + inst22t.getCodeOffset(), constants[inst22t.getRegisterB()], method.getImplementation().getRegisterCount());
				} else if(in.getOpcode().equals(Opcode.IF_NE) && constants[inst22t.getRegisterA()] != null) {
					current = new codeBlock(indexPointer, indexPointer + inst22t.getCodeOffset(), constants[inst22t.getRegisterA()], method.getImplementation().getRegisterCount());
				}
				break;
			case Format22x :
				Instruction22x inst22x = (Instruction22x) in;
				registerClasses[inst22x.getRegisterA()] = registerClasses[inst22x.getRegisterB()];
				constants[inst22x.getRegisterA()] = constants[inst22x.getRegisterB()];
				break;
			case Format23x :
				indexPointer = indexPointer+ 2;
				Instruction23x inst23x = (Instruction23x) in;
				if(in.getOpcode().equals(Opcode.AGET) ||in.getOpcode().equals(Opcode.AGET_BOOLEAN) || in.getOpcode().equals(Opcode.AGET_BYTE) || in.getOpcode().equals(Opcode.AGET_CHAR)
						|| in.getOpcode().equals(Opcode.AGET_OBJECT) || in.getOpcode().equals(Opcode.AGET_SHORT) || in.getOpcode().equals(Opcode.AGET_WIDE)) {
					registerClasses[inst23x.getRegisterA()] = registerClasses[inst23x.getRegisterB()].substring(1);
				} else if(in.getOpcode().equals(Opcode.ADD_LONG) || in.getOpcode().equals(Opcode.SUB_LONG) || in.getOpcode().equals(Opcode.MUL_LONG)
						|| in.getOpcode().equals(Opcode.DIV_LONG) || in.getOpcode().equals(Opcode.REM_LONG) || in.getOpcode().equals(Opcode.AND_LONG)
						|| in.getOpcode().equals(Opcode.OR_LONG) || in.getOpcode().equals(Opcode.XOR_LONG)  || in.getOpcode().equals(Opcode.SHL_LONG)
						|| in.getOpcode().equals(Opcode.SHR_LONG) || in.getOpcode().equals(Opcode.USHR_LONG)) {
					registerClasses[inst23x.getRegisterA()] = "J";
				} else if(in.getOpcode().equals(Opcode.ADD_FLOAT) || in.getOpcode().equals(Opcode.SUB_FLOAT) || in.getOpcode().equals(Opcode.MUL_FLOAT) 
						|| in.getOpcode().equals(Opcode.DIV_FLOAT) || in.getOpcode().equals(Opcode.REM_FLOAT)) {
					registerClasses[inst23x.getRegisterA()] = "F";
				} else if(in.getOpcode().equals(Opcode.ADD_DOUBLE) || in.getOpcode().equals(Opcode.SUB_DOUBLE) || in.getOpcode().equals(Opcode.MUL_DOUBLE)
						|| in.getOpcode().equals(Opcode.DIV_DOUBLE) || in.getOpcode().equals(Opcode.REM_DOUBLE)) {
					registerClasses[inst23x.getRegisterA()] = "D";
				} else {
					registerClasses[inst23x.getRegisterA()] = "I";
				}
				break;
			case Format30t :
				Instruction30t inst30t = (Instruction30t) in;
				break;
			case Format31c :
				Instruction31c inst31c = (Instruction31c) in;
				registerClasses[inst31c.getRegisterA()] = getTypeFromName(String.class.getTypeName());
				constants[inst31c.getRegisterA()] = inst31c.getReference().toString();
				break;
			case Format31i :
				Instruction31i inst31i = (Instruction31i) in;
				if(in.getOpcode().equals(Opcode.CONST)) {
					registerClasses[inst31i.getRegisterA()] = "I";
					constants[inst31i.getRegisterA()] = Integer.toString(inst31i.getNarrowLiteral());
				} else {
					registerClasses[inst31i.getRegisterA()] = "J";
					constants[inst31i.getRegisterA()] = Long.toString(inst31i.getWideLiteral());
				}
				break;
			case Format31t :
				Instruction31t inst31t = (Instruction31t) in;
				break;
			case Format32x :
				Instruction32x inst32x = (Instruction32x) in;
				registerClasses[inst32x.getRegisterA()] = registerClasses[inst32x.getRegisterB()];
				constants[inst32x.getRegisterA()] = constants[inst32x.getRegisterB()];
				break;
			case Format35c :
				Instruction35c inst35c = (Instruction35c) in;
				if (in.getOpcode().equals(Opcode.FILLED_NEW_ARRAY)) {
					returnType = inst35c.getReference().toString();
				} else {
					if (!inst35c.getReference().toString().substring(inst35c.getReference().toString().lastIndexOf(")") +1).equals("V") ) {
						returnType = inst35c.getReference().toString().substring(inst35c.getReference().toString().lastIndexOf(")") + 1);
					}
				}
				break;
			case Format35mi :
				System.out.println("35mi: "+in.getOpcode()+"Not handled, dangerous");
				//No opcode with this format?
				break;
			case Format35ms :
				System.out.println("35ms: "+in.getOpcode()+"Not handled, dagnerous");
				break;
			case Format3rc :
				Instruction3rc inst3rc = (Instruction3rc) in;
				if(in.getOpcode().equals(Opcode.FILLED_NEW_ARRAY_RANGE)) {
					returnType = inst3rc.getReference().toString();
				} else if (!inst3rc.getReference().toString().substring(inst3rc.getReference().toString().lastIndexOf(")") +1).equals("V")) {
					returnType = inst3rc.getReference().toString().substring(inst3rc.getReference().toString().lastIndexOf(")") + 1);
				}
				break;
			case Format3rmi :
				System.out.println("3rmi :"+in.getOpcode()+ "Not handled, dangerous");
				break;
			case Format3rms :
				System.out.println("3rms :"+in.getOpcode()+ "Not handled, dangerous");
				break;
			case Format45cc :
				Instruction45cc inst45cc = (Instruction45cc) in;
				returnType = inst45cc.getReference2().toString().substring(inst45cc.getReference2().toString().lastIndexOf(")") +1);
				break;
			case Format4rcc :
				Instruction4rcc inst4rcc = (Instruction4rcc) in;
				returnType = inst4rcc.getReference2().toString().substring(inst4rcc.getReference2().toString().lastIndexOf(")") +1);
				break;
			case Format51l :
				Instruction51l inst51l = (Instruction51l) in;
				registerClasses[inst51l.getRegisterA()] = "D";
				constants[inst51l.getRegisterA()] = Long.toString(inst51l.getWideLiteral());
				break;
			default :
				
			}
			instructionsize = getInstructionSize(in);
			indexPointer = indexPointer + instructionsize;
		}
		return result;
	}
	
	public static class codeBlock {
		public boolean rejected = false;
		public int start;
		public int end;
		public String key;
		public boolean[] registersActive;
		public String[] startClasses;
		public String[] endClasses;
		List<Instruction> instructions;
		codeBlock(int s, int e, String k, int registerNumber) {
			this.start = s;
			this.end = e;
			this.key = k;
			this.registersActive = new boolean[registerNumber];
			this.startClasses = new String[registerNumber];
			this.endClasses = new String[registerNumber];
			instructions = new LinkedList<Instruction>();
		}
		
		public int paramsize () {
			int i = 0;
			for(String s : startClasses) {
				if (s != null) {
					i++;
				}
			}
			return i;
		}
		
		public int paraPrim () {
			int i = 0;
			for(String s : startClasses) {
				if (!(s.contains("L") || s.contains("["))) {
					i++;
				}
			}
			return i;
		}
		
		public int arrPrim () {
			int i = 0;
			for(String s : endClasses) {
				if (s != null) {
				if (!(s.contains("L") || s.contains("["))) {
					i++;
				}
				}
			}
			return i;
		}
		
		public int arrsize () {
			int i = 0;
			for(String s : endClasses) {
				if(s != null) {
					i++;
				}
			}
			return i;
		}
		
		public int blocksize () {
			return end - start - (23 + 8*paramsize() + 4*paraPrim() + 3*arrsize() + 4*arrPrim() + 2*(arrsize() - arrPrim()));
		}
	}
	
	public static class tInstruction {
		public int start;
		public int end;
		public boolean SDC;
		tInstruction (int s, int e, boolean sdc) {
			this.start = s;
			this.end = e;
			this.SDC = sdc;
		}
	}

	private static List<tInstruction> getTInstructions(Method m) {
		int index = 0;
		List<tInstruction> result = new LinkedList<tInstruction>();
		//TODO: Annotations/try-catch-blocks
		for(Instruction in : m.getImplementation().getInstructions()) {
			switch (in.getOpcode().format) {
			case Format10t :
				Instruction10t inst10t = (Instruction10t) in;
				result.add(new tInstruction(index, index + inst10t.getCodeOffset(), false));
				break;
			case Format20t :
				Instruction20t inst20t = (Instruction20t) in;
				result.add(new tInstruction(index, index + inst20t.getCodeOffset(), false));
				break;
			case Format21t :
				Instruction21t inst21t = (Instruction21t) in;
				result.add(new tInstruction(index, index + inst21t.getCodeOffset(), in.getOpcode().equals(Opcode.IF_NEZ)));
				break;
			case Format22t :
				Instruction22t inst22t = (Instruction22t) in;
				result.add(new tInstruction(index, index + inst22t.getCodeOffset(), in.getOpcode().equals(Opcode.IF_NE)));
				break;
			case Format30t :
				Instruction30t inst30t = (Instruction30t) in;
				result.add(new tInstruction(index, index + inst30t.getCodeOffset(), false));
				break;
			case Format31t :
				Instruction31t inst31t = (Instruction31t) in;
				result.add(new tInstruction(index, index + inst31t.getCodeOffset(), false));
				break;
			default :
				
			}
			index = index + getInstructionSize(in);
		}

		return result;
		}
	
	
	private static String getTypeFromName(String name) {
		return "L" + name.replace(".", "/") + ";";
	}
	
	private static int getInstructionSize(Instruction in) {
		switch (in.getOpcode().format) {
		case Format10t :
			return 1;
		case Format10x :
			return 1;
		case Format11n :
			return 1;
		case Format11x :
			return 1;
		case Format12x :
			return 1;
		case Format20bc :
			return 2;
		case Format20t :
			return 2;
		case Format21c :
			return 2;
		case Format21ih :
			return 2;
		case Format21lh :
			return 2;
		case Format21s :
			return 2;
		case Format21t :
			return 2;
		case Format22b :
			return 2;
		case Format22c :
			return 2;
		case Format22cs :
			return 2;
		case Format22s :
			return 2;
		case Format22t :
			return 2;
		case Format22x :
			return 2;
		case Format23x :
			return 2;
		case Format30t :
			return 3;
		case Format31c :
			return 3;
		case Format31i :
			return 3;
		case Format31t :
			return 3;
		case Format32x :
			return 3;
		case Format35c :
			return 3;
		case Format35mi :
			return 3;
		case Format35ms :
			return 3;
		case Format3rc :
			return 3;
		case Format3rmi :
			return 3;
		case Format3rms :
			return 3;
		case Format45cc :
			return 4;
		case Format4rcc :
			return 4;
		case Format51l :
			return 5;
		case ArrayPayload :
			ArrayPayload pld = (ArrayPayload) in;
			return (pld.getArrayElements().size() * pld.getElementWidth() +1)/2 +4;
		case PackedSwitchPayload :
			PackedSwitchPayload pspld = (PackedSwitchPayload) in;
			return (pspld.getSwitchElements().size()*2) + 4;
		case SparseSwitchPayload :
			SparseSwitchPayload sspld = (SparseSwitchPayload) in;
			return (sspld.getSwitchElements().size() *4) + 2;
		default : 
			return 0;
		}
	}
	private static void writeCodeBlock(codeBlock codeblock, String name, Method method, ClassDef clazz) {
		List<Instruction> instructions = new LinkedList<Instruction>();
		int[] newPosition = new int[codeblock.startClasses.length];
		int arrayHandlingSize = 2;
		int i = 0;
		int j = 0;
		int p = 0;
		for(String param : codeblock.startClasses) {
			if(param == null) {
				newPosition[i] = j+arrayHandlingSize;
				j++;
			} else {
				newPosition[i] = arrayHandlingSize + codeblock.startClasses.length - codeblock.paramsize()+p;
				p++;
			}
			i++;
		}
		for(Instruction in : codeblock.instructions) {
			switch(in.getOpcode().format) {
			case Format11x :
				Instruction11x inst11x = (Instruction11x) in;
				instructions.add(new ImmutableInstruction11x(in.getOpcode(), newPosition[inst11x.getRegisterA()]));
				break;
			case Format11n :
				Instruction11n inst11n = (Instruction11n) in;
				instructions.add(new ImmutableInstruction11n(in.getOpcode(), newPosition[inst11n.getRegisterA()], inst11n.getNarrowLiteral()));
				break;
			case Format12x :
				Instruction12x inst12x = (Instruction12x) in;
				instructions.add(new ImmutableInstruction12x(in.getOpcode(), newPosition[inst12x.getRegisterA()], newPosition[inst12x.getRegisterB()]));
				break;
			case Format21c :
				Instruction21c inst21c = (Instruction21c) in;
				instructions.add(new ImmutableInstruction21c(in.getOpcode(), newPosition[inst21c.getRegisterA()], inst21c.getReference()));
				break;
			case Format21ih :
				Instruction21ih inst21h = (Instruction21ih) in;
				instructions.add(new ImmutableInstruction21ih(in.getOpcode(), newPosition[inst21h.getRegisterA()], inst21h.getNarrowLiteral()));
				break;
			case Format21lh :
				Instruction21lh inst21lh = (Instruction21lh) in;
				instructions.add(new ImmutableInstruction21lh(in.getOpcode(), newPosition[inst21lh.getRegisterA()], inst21lh.getWideLiteral()));
				break;
			case Format21s :
				Instruction21s inst21s = (Instruction21s) in;
				instructions.add(new ImmutableInstruction21s(in.getOpcode(), newPosition[inst21s.getRegisterA()], inst21s.getNarrowLiteral()));
				break;
			case Format21t :
				Instruction21t inst21t = (Instruction21t) in;
				instructions.add(new ImmutableInstruction21t(in.getOpcode(), newPosition[inst21t.getRegisterA()], inst21t.getCodeOffset()));
				break;
			case Format22b :
				Instruction22b inst22b = (Instruction22b) in;
				instructions.add(new ImmutableInstruction22b(in.getOpcode(), newPosition[inst22b.getRegisterA()], newPosition[inst22b.getRegisterB()], inst22b.getNarrowLiteral()));
				break;
			case Format22c :
				Instruction22c inst22c = (Instruction22c) in;
				instructions.add(new ImmutableInstruction22c(in.getOpcode(), newPosition[inst22c.getRegisterA()], newPosition[inst22c.getRegisterB()], inst22c.getReference()));
				break;
			case Format22cs :
				Instruction22cs inst22cs = (Instruction22cs) in;
				instructions.add(new ImmutableInstruction22cs(in.getOpcode(), newPosition[inst22cs.getRegisterA()], newPosition[inst22cs.getRegisterB()], inst22cs.getFieldOffset()));
				break;
			case Format22s :
				Instruction22s inst22s = (Instruction22s) in;
				instructions.add(new ImmutableInstruction22s(in.getOpcode(), newPosition[inst22s.getRegisterA()], newPosition[inst22s.getRegisterB()], inst22s.getNarrowLiteral()));
				break;
			case Format22t :
				Instruction22t inst22t = (Instruction22t) in;
				instructions.add(new ImmutableInstruction22t(in.getOpcode(), newPosition[inst22t.getRegisterA()], newPosition[inst22t.getRegisterB()], inst22t.getCodeOffset()));
				break;
			case Format22x :
				Instruction22x inst22x = (Instruction22x) in;
				instructions.add(new ImmutableInstruction22x(in.getOpcode(), newPosition[inst22x.getRegisterA()], newPosition[inst22x.getRegisterB()]));
				break;
			case Format23x :
				Instruction23x inst23x = (Instruction23x) in;
				instructions.add(new ImmutableInstruction23x(in.getOpcode(), newPosition[inst23x.getRegisterA()], newPosition[inst23x.getRegisterB()], newPosition[inst23x.getRegisterC()]));
				break;
			case Format31c :
				Instruction31c inst31c = (Instruction31c) in;
				instructions.add(new ImmutableInstruction31c(in.getOpcode(), newPosition[inst31c.getRegisterA()], inst31c.getReference()));
				break;
			case Format31i :
				Instruction31i inst31i = (Instruction31i) in;
				instructions.add(new ImmutableInstruction31i(in.getOpcode(), newPosition[inst31i.getRegisterA()], inst31i.getNarrowLiteral()));
				break;
			case Format31t :
				Instruction31t inst31t = (Instruction31t) in;
				instructions.add(new ImmutableInstruction31t(in.getOpcode(), newPosition[inst31t.getRegisterA()], inst31t.getCodeOffset()));
				break;
			case Format32x :
				Instruction32x inst32x = (Instruction32x) in;
				instructions.add(new ImmutableInstruction32x(in.getOpcode(), newPosition[inst32x.getRegisterA()], newPosition[inst32x.getRegisterB()]));
				break;
			case Format35c :
				Instruction35c inst35c = (Instruction35c) in;
				instructions.add(new ImmutableInstruction35c(in.getOpcode(), inst35c.getRegisterCount(), newPosition[inst35c.getRegisterC()], 
						newPosition[inst35c.getRegisterD()], newPosition[inst35c.getRegisterE()], newPosition[inst35c.getRegisterF()], newPosition[inst35c.getRegisterG()], inst35c.getReference()));
				break;
			case Format35mi :
				Instruction35mi inst35mi = (Instruction35mi) in;
				instructions.add(new ImmutableInstruction35mi(in.getOpcode(), inst35mi.getRegisterCount(), newPosition[inst35mi.getRegisterC()], newPosition[inst35mi.getRegisterD()], 
						newPosition[inst35mi.getRegisterE()], newPosition[inst35mi.getRegisterF()], newPosition[inst35mi.getRegisterG()], inst35mi.getInlineIndex()));
				break;
			case Format35ms :
				Instruction35ms inst35ms = (Instruction35ms) in;
				instructions.add(new ImmutableInstruction35ms(in.getOpcode(), inst35ms.getRegisterCount(), newPosition[inst35ms.getRegisterC()], newPosition[inst35ms.getRegisterD()], 
						newPosition[inst35ms.getRegisterE()], newPosition[inst35ms.getRegisterF()], newPosition[inst35ms.getRegisterG()], inst35ms.getVtableIndex()));
				break;
			/*case Format45cc :
				Instruction45cc inst45cc = (Instruction45cc) in;
				instructions.add(new ImmutableInstruction45cc());
				break;*/
				//TODO: implement my own ImmutableInstruction class for 45cc
			case Format51l :
				Instruction51l inst51l = (Instruction51l) in;
				instructions.add(new ImmutableInstruction51l(in.getOpcode(), newPosition[inst51l.getRegisterA()], inst51l.getWideLiteral()));
				break;
			default :
				instructions.add(in);
				break;
			}
		}
		instructions.add(new ImmutableInstruction11n(Opcode.CONST_4, 0, codeblock.arrsize()));
		instructions.add(new ImmutableInstruction22c(Opcode.NEW_ARRAY, 0, 0, new ImmutableTypeReference("[Ljava/lang/Object;")));
		i = 0;
		j = 0;
		for(String s : codeblock.endClasses) {
			if(s != null) {
				List<String> param = new LinkedList<String>();
				switch (s) {
				case "I" :
					param.add("I");
					instructions.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, newPosition[j], 0, 0, 0, 0, 									
							new ImmutableMethodReference("Ljava/lang/Integer;", "valueOf", param, "Ljava/lang/Integer;")));
					instructions.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, newPosition[j]));
					break;
				case "J" :
					param.add("J");
					instructions.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, newPosition[j], 0, 0, 0, 0, 									
							new ImmutableMethodReference("Ljava/lang/Long;", "valueOf", param, "Ljava/lang/Long;")));
					instructions.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, newPosition[j]));
					break;
				case "Z" :
					param.add("Z");
					instructions.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, newPosition[j], 0, 0, 0, 0, 									
							new ImmutableMethodReference("Ljava/lang/Boolean;", "valueOf", param, "Ljava/lang/Boolean;")));
					instructions.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, newPosition[j]));
					break;
				case "F" :
					param.add("F");
					instructions.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, newPosition[j], 0, 0, 0, 0, 									
							new ImmutableMethodReference("Ljava/lang/Float;", "valueOf", param, "Ljava/lang/Float;")));
					instructions.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, newPosition[j]));
					break;
				case "D" :
					param.add("D");
					instructions.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, newPosition[j], 0, 0, 0, 0, 									
							new ImmutableMethodReference("Ljava/lang/Double;", "valueOf", param, "Ljava/lang/Double;")));
					instructions.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, newPosition[j]));
					break;
				default :
					break;
				}
				instructions.add(new ImmutableInstruction11n(Opcode.CONST_4, 1, i));
				instructions.add(new ImmutableInstruction23x(Opcode.APUT_OBJECT, newPosition[j], 0, 1));
				i++;
			}
			j++;
		}
		instructions.add(new ImmutableInstruction11x(Opcode.RETURN_OBJECT, 0));
		List<MethodParameter> parameters = new LinkedList<MethodParameter>();
		for (String parameter : codeblock.startClasses) {
			if (parameter != null) {
				parameters.add(new ImmutableMethodParameter(parameter, null, null));
			}
		}
		if (parameters.isEmpty()) {
			parameters = null;
		}
		MethodImplementation impl = new ImmutableMethodImplementation(codeblock.endClasses.length+arrayHandlingSize, instructions, null, null);
		Method m = new ImmutableMethod("SDC/ImportClass", name, parameters, "[Ljava/lang/Object;", 9, null, impl);
		//implement tryblock handling
		encodedBlocks.add(m);
	}
	
	private static List<Instruction> replaceCodeBlock(codeBlock codeblock, String name, Method m, ClassDef c, List<Instruction> instructions) {
		List<Instruction> result = new LinkedList<Instruction>();
		int indexPointer = 0;
		int codeblocksize = codeblock.blocksize();
		for(Instruction in : instructions) {
			if(indexPointer<codeblock.start || indexPointer>=codeblock.end) {
			switch(in.getOpcode().format) {
			case Format10t :
				Instruction10t inst10t = (Instruction10t) in;
				if(indexPointer < codeblock.start && inst10t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction10t(in.getOpcode(), inst10t.getCodeOffset()-codeblocksize));
				} else if(indexPointer > codeblock.end && inst10t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction10t(in.getOpcode(), inst10t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			case Format20t :
				Instruction20t inst20t = (Instruction20t) in;
				if(indexPointer < codeblock.start && inst20t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction20t(in.getOpcode(), inst20t.getCodeOffset()-codeblocksize));
				} else if (indexPointer > codeblock.end && inst20t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction20t(in.getOpcode(), inst20t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			case Format21t :
				Instruction21t inst21t = (Instruction21t) in;
				if(indexPointer < codeblock.start && inst21t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction21t(in.getOpcode(), inst21t.getRegisterA(), inst21t.getCodeOffset()-codeblocksize));
				} else if (indexPointer > codeblock.end && inst21t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction21t(in.getOpcode(), inst21t.getRegisterA(), inst21t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			case Format22t :
				Instruction22t inst22t = (Instruction22t) in;
				if(indexPointer < codeblock.start && inst22t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction22t(in.getOpcode(), inst22t.getRegisterA(), inst22t.getRegisterB(), inst22t.getCodeOffset()-codeblocksize));
				} else if (indexPointer > codeblock.end && inst22t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction22t(in.getOpcode(), inst22t.getRegisterA(), inst22t.getRegisterB(), inst22t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			case Format30t :
				Instruction30t inst30t = (Instruction30t) in;
				if(indexPointer < codeblock.start && inst30t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction30t(in.getOpcode(), inst30t.getCodeOffset()-codeblocksize));
				} else if (indexPointer > codeblock.end && inst30t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction30t(in.getOpcode(), inst30t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			case Format31t :
				Instruction31t inst31t = (Instruction31t) in;
				if(indexPointer < codeblock.start && inst31t.getCodeOffset()+indexPointer > codeblock.end) {
					result.add(new ImmutableInstruction31t(in.getOpcode(), inst31t.getRegisterA(), inst31t.getCodeOffset()-codeblocksize));
				} else if (indexPointer > codeblock.end && inst31t.getCodeOffset()+indexPointer < codeblock.start) {
					result.add(new ImmutableInstruction31t(in.getOpcode(), inst31t.getRegisterA(), inst31t.getCodeOffset()+codeblocksize));
				} else {
					result.add(in);
				}
				break;
			default :
				result.add(in);
				break;
			}
			} else if(indexPointer == codeblock.start){
					
				if(in.getOpcode().equals(Opcode.IF_NEZ)) {
					Instruction21t inst21t = (Instruction21t) in;
					result.add(new ImmutableInstruction21t(Opcode.IF_NEZ, inst21t.getRegisterA(), inst21t.getCodeOffset() - (codeblocksize)));
				} else if (in.getOpcode().equals(Opcode.IF_NE)) {
					Instruction22t inst22t = (Instruction22t) in;
					result.add(new ImmutableInstruction22t(Opcode.IF_NE, inst22t.getRegisterA(), inst22t.getRegisterB(), inst22t.getCodeOffset() - (codeblocksize)));
				}
				
				
				//check cast?
				result.add(new ImmutableInstruction11n(Opcode.CONST_4, 2, codeblock.paramsize()));
				result.add(new ImmutableInstruction22c(Opcode.NEW_ARRAY, 2, 2, new ImmutableTypeReference("[Ljava/lang/Class;")));
				int i = 0; //NO: 5
				List<String> paraList = new LinkedList<String>();
				for(String clazz : codeblock.startClasses) {
					if(clazz != null) {
					paraList.add(clazz);
					Reference ref;
					Opcode opc = Opcode.SGET_OBJECT;
							switch (clazz) {
							case "I" :
								ref = new ImmutableFieldReference("Ljava/lang/Integer;", "TYPE", "Ljava/lang/Class;");
								break;
							case "Z" :
								ref = new ImmutableFieldReference("Ljava/lang/Boolean;", "TYPE", "Ljava/lang/Class;");
								break;
							case "J" :
								ref = new ImmutableFieldReference("Ljava/lang/Long;", "TYPE", "Ljava/lang/Class;");
								break;
							case "F" :
								ref = new ImmutableFieldReference("Ljava/lang/Float;", "TYPE", "Ljava/lang/Class;");
								break;
							case "D" :
								ref = new ImmutableFieldReference("Ljava/lang/Double;", "TYPE", "Ljava/lang/Class;");
								break;
							default :
								ref = new ImmutableTypeReference(clazz);
								opc = Opcode.CONST_CLASS;
							}
							result.add(new ImmutableInstruction11n(Opcode.CONST_4, 0, i));
							result.add(new ImmutableInstruction21c(opc, 1, ref));
							result.add(new ImmutableInstruction23x(Opcode.APUT_OBJECT, 1, 2, 0));

					i++; //NO: 5 per startclass entry
					}
				}
				List<String> l = new LinkedList<String>();
				l.add("Landroid/support/v7/app/AppCompatActivity;");
				result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, m.getImplementation().getRegisterCount()+3-m.getParameters().size()-1, 0, 0, 0, 0, 
						 new ImmutableMethodReference("LSDC/FileLoader;", "loadClass", l, "Ljava/lang/Class;")));
				result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, 0));
				result.add(new ImmutableInstruction21c(Opcode.CONST_STRING, 1, new ImmutableStringReference(name)));
				l.clear();
				l.add("Ljava/lang/String;");
				l.add("[Ljava/lang/Class;");
				result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 3, 0, 1, 2, 0, 0, 
						new ImmutableMethodReference("Ljava/lang/Class;", "getMethod", l, "Ljava/lang/reflect/Method;")));
				//potentially false registercount?
				result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, 2));
				result.add(new ImmutableInstruction11n(Opcode.CONST_4, 1, codeblock.paramsize()));
				result.add(new ImmutableInstruction22c(Opcode.NEW_ARRAY, 1, 1, new ImmutableTypeReference("[Ljava/lang/Object;")));
				//NO: 13
				i = 0;
				int j = 0;
				for(String clazz : codeblock.startClasses) {
					if(clazz != null) {
						result.add(new ImmutableInstruction11n(Opcode.CONST_4, 0, i));
						List<String> param = new LinkedList<String>();
						if (!(clazz.contains("L") || clazz.contains("["))) {
							switch(clazz) {
							case "I" :
							param.add("I");
							result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, 3+j, 0, 0, 0, 0, 									
									new ImmutableMethodReference("Ljava/lang/Integer;", "valueOf", param, "Ljava/lang/Integer;")));
							break;
							case "J" :
								param.add("J");
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, 3+j, 0, 0, 0, 0, 									
										new ImmutableMethodReference("Ljava/lang/Long;", "valueOf", param, "Ljava/lang/Long;")));
								break;
							case "Z" :
								param.add("Z");
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, 3+j, 0, 0, 0, 0, 									
										new ImmutableMethodReference("Ljava/lang/Boolean;", "valueOf", param, "Ljava/lang/Boolean;")));
								break;
							case "F" :
								param.add("F");
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, 3+j, 0, 0, 0, 0, 									
										new ImmutableMethodReference("Ljava/lang/Float;", "valueOf", param, "Ljava/lang/Float;")));
								break;
							case "D" :
								param.add("D");
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_STATIC, 1, 3+j, 0, 0, 0, 0, 									
										new ImmutableMethodReference("Ljava/lang/Double;", "valueOf", param, "Ljava/lang/Double;")));
								break;
							}
							result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, 3+j));
							
						}
						result.add(new ImmutableInstruction23x(Opcode.APUT_OBJECT, 3+j, 1, 0));
						i++; //NO: 3 for each entry in startclasses, additional 4 for each primitive entry
					}
					j++;
				}
				result.add(new ImmutableInstruction11n(Opcode.CONST_4, 0, 0));
				l.clear();
				l.add("Ljava/lang/Object;");
				l.add("[Ljava/lang/Object;");
				result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 3, 2, 0, 1, 0, 0,
						new ImmutableMethodReference("Ljava/lang/reflect/Method;", "invoke", l, "[Ljava/lang/Object;")));
				result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_OBJECT, 2)); //NO: 5
				i = 0;
				j = 0;
				for(String clazz : codeblock.endClasses) {
					if(clazz != null) {
						result.add(new ImmutableInstruction11n(Opcode.CONST_4, 0, i));
						result.add(new ImmutableInstruction23x(Opcode.AGET_OBJECT, 3+j, 2, 0));
						//NO: 3 for each entry in endclasses, additional 4 for primitives and 2 for objects
						if(!(clazz.contains("L") || clazz.contains("["))) {
							switch (clazz) {
							case "I" :
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 1, 3+j, 0, 0, 0, 0, 
										new ImmutableMethodReference("Ljava/lang/Integer;", "intValue", null, "I")));
								result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT, 3+j));
								break;
							case "Z" :
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 1, 3+j, 0, 0, 0, 0, 
										new ImmutableMethodReference("Ljava/lang/Boolean;", "booleanValue", null, "Z")));
								result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT, 3+j));
								break;
							case "J" :
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 1, 3+j, 0, 0, 0, 0, 
										new ImmutableMethodReference("Ljava/lang/Long;", "longValue", null, "J")));
								result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_WIDE, 3+j));
								break;
							case "F" :
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 1, 3+j, 0, 0, 0, 0, 
										new ImmutableMethodReference("Ljava/lang/Float;", "floatValue", null, "F")));
								result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_WIDE, 3+j));
								break;
							case "D" :
								result.add(new ImmutableInstruction35c(Opcode.INVOKE_VIRTUAL, 1, 3+j, 0, 0, 0, 0, 
										new ImmutableMethodReference("Ljava/lang/Double;", "doubleValue", null, "D")));
								result.add(new ImmutableInstruction11x(Opcode.MOVE_RESULT_WIDE, 3+j));
								break;
							}
						} else {
							result.add(new ImmutableInstruction21c(Opcode.CHECK_CAST, 3+j, new ImmutableTypeReference(clazz)));
						}
						i++;
					}
					j++;
				}
			}
			indexPointer = indexPointer + getInstructionSize(in);
			
		}
		return result;
	}
	
	private static Method adjustedMethod(ClassDef c, Method m) {
		boolean codeblocks = false;
		if(m.getImplementation() != null) {
			int i = 0;
		List<Instruction> instructions =  new LinkedList<Instruction>();
		m.getImplementation().getInstructions().iterator().forEachRemaining(instructions::add);
		List<TryBlock> tryblocks = new LinkedList<TryBlock>();
		m.getImplementation().getTryBlocks().iterator().forEachRemaining(tryblocks::add);
		LinkedList<codeBlock> list = getSDCBlocks(m);
		List<tInstruction> jumps = getTInstructions(m);
		Iterator<codeBlock> iter = list.descendingIterator();
		while(iter.hasNext()) {
			codeBlock cb = iter.next();
			if (cb.start > cb.end) {
				cb.rejected = true;
			}
			for(tInstruction t :jumps) {
				int s = Math.min(t.start, t.end);
				int e = Math.max(t.start, t.end);
				if(s < cb.start && cb.start < e && e < cb.end) {
					cb.rejected = true;
				} else if (cb.start < s && s < cb.end && cb.end < e) {
					cb.rejected = true;
				}
			}
			if(!cb.rejected) {
				if(codeblocks == false) {
					instructions = shiftRegisters(instructions, 3);
					codeblocks = true;
				}
				System.out.println("Accepted codeblock in "+m.getName());
				writeCodeBlock(cb, m.getName()+ i, m, c);
				instructions = replaceCodeBlock(cb, m.getName()+i, m, c, instructions);
				List<TryBlock> tb = new LinkedList<TryBlock>();
				for (TryBlock t : tryblocks) {
					List<ExceptionHandler> handlers = new LinkedList<ExceptionHandler>();
					for (ExceptionHandler h : (List<ExceptionHandler>) t.getExceptionHandlers()) {
						if (h.getHandlerCodeAddress() > cb.end) {
						handlers.add(new ImmutableExceptionHandler(h.getExceptionType(), h.getHandlerCodeAddress()-cb.blocksize()));
						} else {
							handlers.add(h);
						}		
					}
					if(t.getStartCodeAddress() > cb.start && t.getStartCodeAddress() < cb.end) {
						
					} else if (t.getStartCodeAddress() >= cb.end) {
						tb.add(new ImmutableTryBlock(t.getStartCodeAddress()-cb.blocksize(), t.getCodeUnitCount(), handlers));
					} else if (t.getStartCodeAddress()< cb.start && t.getStartCodeAddress()+t.getCodeUnitCount() > cb.end){
						tb.add(new ImmutableTryBlock(t.getStartCodeAddress(), t.getCodeUnitCount()-cb.blocksize(), handlers));
					} else {
						tb.add(new ImmutableTryBlock(t.getStartCodeAddress(), t.getCodeUnitCount(), handlers));
					}
				}
				System.out.println(cb.start + " " + cb.end + " " + cb.blocksize()) ;
				int msize = methodSize(m) - cb.blocksize();
				int s = cb.end - cb.start - cb.blocksize();
				List<ExceptionHandler> h = new LinkedList<ExceptionHandler>();
				
				h.add(new ImmutableExceptionHandler("Ljava/lang/reflect/InvocationTargetException;", msize));
				instructions.add(new ImmutableInstruction11x(Opcode.MOVE_EXCEPTION, 0));
				instructions.add(new ImmutableInstruction10t(Opcode.GOTO, -(msize + 1 - cb.start - s )));
				h.add(new ImmutableExceptionHandler("Ljava/lang/IllegalAccessException;", msize + 2));
				instructions.add(new ImmutableInstruction11x(Opcode.MOVE_EXCEPTION, 0));
				instructions.add(new ImmutableInstruction10t(Opcode.GOTO, -(msize + 3 - cb.start - s )));
				h.add(new ImmutableExceptionHandler("Ljava/lang/NoSuchMethodException;", msize + 4));
				instructions.add(new ImmutableInstruction11x(Opcode.MOVE_EXCEPTION, 0));
				instructions.add(new ImmutableInstruction10t(Opcode.GOTO, -(msize + 5 - cb.start - s )));
				tb.add(new ImmutableTryBlock(cb.start+2, s -2, h));
				tryblocks = tb;
			}
		}
		if (codeblocks) {
			return new ImmutableMethod(m.getDefiningClass(), m.getName(), m.getParameters(), m.getReturnType(), m.getAccessFlags(), m.getAnnotations(), 
					new ImmutableMethodImplementation(m.getImplementation().getRegisterCount()+3, instructions, (List<? extends TryBlock<? extends ExceptionHandler>>) tryblocks, null));
		} else {
			return m;
		}
		} else {
			return m;
		}
		
	
			
	}
	
	private static int methodSize(Method m) {
		int i = 0;
		for (Instruction in : m.getImplementation().getInstructions()) {
			i = i + getInstructionSize(in);
		}
		return i;
	}
	
	private static List<Instruction> shiftRegisters(List<Instruction> l, int s) {
		List<Instruction> instructions = new LinkedList<Instruction>();
		for(Instruction in : l) {
			switch(in.getOpcode().format) {
			case Format11x :
				Instruction11x inst11x = (Instruction11x) in;
				instructions.add(new ImmutableInstruction11x(in.getOpcode(), inst11x.getRegisterA() + s));
				break;
			case Format11n :
				Instruction11n inst11n = (Instruction11n) in;
				instructions.add(new ImmutableInstruction11n(in.getOpcode(), inst11n.getRegisterA() + s, inst11n.getNarrowLiteral()));
				break;
			case Format12x :
				Instruction12x inst12x = (Instruction12x) in;
				instructions.add(new ImmutableInstruction12x(in.getOpcode(), inst12x.getRegisterA() + s, inst12x.getRegisterB() + s));
				break;
			case Format21c :
				Instruction21c inst21c = (Instruction21c) in;
				instructions.add(new ImmutableInstruction21c(in.getOpcode(), inst21c.getRegisterA() + s, inst21c.getReference()));
				break;
			case Format21ih :
				Instruction21ih inst21h = (Instruction21ih) in;
				instructions.add(new ImmutableInstruction21ih(in.getOpcode(), inst21h.getRegisterA() + s, inst21h.getNarrowLiteral()));
				break;
			case Format21lh :
				Instruction21lh inst21lh = (Instruction21lh) in;
				instructions.add(new ImmutableInstruction21lh(in.getOpcode(), inst21lh.getRegisterA() + s, inst21lh.getWideLiteral()));
				break;
			case Format21s :
				Instruction21s inst21s = (Instruction21s) in;
				instructions.add(new ImmutableInstruction21s(in.getOpcode(), inst21s.getRegisterA() + s, inst21s.getNarrowLiteral()));
				break;
			case Format21t :
				Instruction21t inst21t = (Instruction21t) in;
				instructions.add(new ImmutableInstruction21t(in.getOpcode(), inst21t.getRegisterA() + s, inst21t.getCodeOffset()));
				break;
			case Format22b :
				Instruction22b inst22b = (Instruction22b) in;
				instructions.add(new ImmutableInstruction22b(in.getOpcode(), inst22b.getRegisterA() + s, inst22b.getRegisterB() + s, inst22b.getNarrowLiteral()));
				break;
			case Format22c :
				Instruction22c inst22c = (Instruction22c) in;
				instructions.add(new ImmutableInstruction22c(in.getOpcode(), inst22c.getRegisterA() + s, inst22c.getRegisterB() + s, inst22c.getReference()));
				break;
			case Format22cs :
				Instruction22cs inst22cs = (Instruction22cs) in;
				instructions.add(new ImmutableInstruction22cs(in.getOpcode(), inst22cs.getRegisterA() + s, inst22cs.getRegisterB() + s, inst22cs.getFieldOffset()));
				break;
			case Format22s :
				Instruction22s inst22s = (Instruction22s) in;
				instructions.add(new ImmutableInstruction22s(in.getOpcode(), inst22s.getRegisterA() + s, inst22s.getRegisterB() + s, inst22s.getNarrowLiteral()));
				break;
			case Format22t :
				Instruction22t inst22t = (Instruction22t) in;
				instructions.add(new ImmutableInstruction22t(in.getOpcode(), inst22t.getRegisterA() + s, inst22t.getRegisterB() + s, inst22t.getCodeOffset()));
				break;
			case Format22x :
				Instruction22x inst22x = (Instruction22x) in;
				instructions.add(new ImmutableInstruction22x(in.getOpcode(), inst22x.getRegisterA() + s, inst22x.getRegisterB() + s));
				break;
			case Format23x :
				Instruction23x inst23x = (Instruction23x) in;
				instructions.add(new ImmutableInstruction23x(in.getOpcode(), inst23x.getRegisterA() + s, inst23x.getRegisterB() + s, inst23x.getRegisterC() + s));
				break;
			case Format31c :
				Instruction31c inst31c = (Instruction31c) in;
				instructions.add(new ImmutableInstruction31c(in.getOpcode(), inst31c.getRegisterA() + s, inst31c.getReference()));
				break;
			case Format31i :
				Instruction31i inst31i = (Instruction31i) in;
				instructions.add(new ImmutableInstruction31i(in.getOpcode(), inst31i.getRegisterA() + s, inst31i.getNarrowLiteral()));
				break;
			case Format31t :
				Instruction31t inst31t = (Instruction31t) in;
				instructions.add(new ImmutableInstruction31t(in.getOpcode(), inst31t.getRegisterA() + s, inst31t.getCodeOffset()));
				break;
			case Format32x :
				Instruction32x inst32x = (Instruction32x) in;
				instructions.add(new ImmutableInstruction32x(in.getOpcode(), inst32x.getRegisterA(), inst32x.getRegisterB() + s));
				break;
			case Format35c :
				Instruction35c inst35c = (Instruction35c) in;
				instructions.add(new ImmutableInstruction35c(in.getOpcode(), inst35c.getRegisterCount(), inst35c.getRegisterC() + s, 
						inst35c.getRegisterD() + s, inst35c.getRegisterE() + s, inst35c.getRegisterF() + s, inst35c.getRegisterG() + s, inst35c.getReference()));
				break;
			case Format35mi :
				Instruction35mi inst35mi = (Instruction35mi) in;
				instructions.add(new ImmutableInstruction35mi(in.getOpcode(), inst35mi.getRegisterCount(), inst35mi.getRegisterC() + s, inst35mi.getRegisterD() + s, 
						inst35mi.getRegisterE() + s, inst35mi.getRegisterF() + s, inst35mi.getRegisterG() + s, inst35mi.getInlineIndex()));
				break;
			case Format35ms :
				Instruction35ms inst35ms = (Instruction35ms) in;
				instructions.add(new ImmutableInstruction35ms(in.getOpcode(), inst35ms.getRegisterCount(), inst35ms.getRegisterC() + s, inst35ms.getRegisterD() + s, 
						inst35ms.getRegisterE() + s, inst35ms.getRegisterF() + s, inst35ms.getRegisterG() + s, inst35ms.getVtableIndex()));
				break;
			/*case Format45cc :
				Instruction45cc inst45cc = (Instruction45cc) in;
				instructions.add(new ImmutableInstruction45cc());
				break;*/
				//TODO: implement my own ImmutableInstruction class for 45cc
			case Format51l :
				Instruction51l inst51l = (Instruction51l) in;
				instructions.add(new ImmutableInstruction51l(in.getOpcode(), inst51l.getRegisterA() + s, inst51l.getWideLiteral()));
				break;
			default :
				instructions.add(in);
				break;
			}
		}
		return instructions;
	}
	
}
