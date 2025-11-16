package com.example;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

public class ByteTokAnalyzer {

    public static void main(String[] args) throws Exception {
        String className = "edu.handong.csee.isel.machinelearning.DNN_node"; // ★ 요청값
        // 로딩: classpath에서 리소스로 읽기 (예: target/classes)
        byte[] bytes = loadClassBytes(className);
        if (bytes == null) {
            System.err.println("[ERROR] Cannot load class bytes for " + className + " from classpath.");
            return;
        }
        List<MethodBytecode> methods = readClass(bytes);

        Gson gson = new GsonBuilder().setPrettyPrinting().create();
        Files.createDirectories(Paths.get("output"));

        for (MethodBytecode mb : methods) {
            Map<String,Object> out = new LinkedHashMap<String,Object>();
            List<Map<String,Object>> nodes = new ArrayList<Map<String,Object>>();
            List<int[]> edgesArr = new ArrayList<int[]>();

            // 노드: insn index, mnem, line
            for (int i = 0; i < mb.insns.size(); i++) {
                Insn insn = mb.insns.get(i);
                Map<String,Object> n = new LinkedHashMap<String,Object>();
                n.put("idx", insn.index);
                n.put("mnemonic", insn.mnemonic);
                n.put("line", insn.line);
                nodes.add(n);
            }
            // 엣지: offset → succ offsets (여기서는 index 기반)
            for (Map.Entry<Integer, List<Integer>> e : mb.edges.entrySet()) {
                int from = e.getKey();
                for (Integer to : e.getValue()) {
                    edgesArr.add(new int[]{from, to});
                }
            }

            out.put("owner", mb.owner);
            out.put("name", mb.name);
            out.put("desc", mb.desc);
            out.put("nodes", nodes);
            out.put("edges", edgesArr);
            out.put("exceptions", mb.exceptionHandlers); // [startIdx,endIdx,handlerIdx]

            String safe = (mb.name.replaceAll("[^a-zA-Z0-9_]", "_"));
            Path p = Paths.get("output", "bytecode_graph_" + safe + ".json");
            Files.write(p, gson.toJson(out).getBytes("UTF-8"));
            System.out.println("✅ Saved " + p.toAbsolutePath());
        }
    }

    // ===== ASM 수집 =====
    static class Insn {
        int index;       // 메서드 내 인스트럭션 순번 (0..N-1)
        int line;        // 라인 번호(없으면 -1)
        String mnemonic; // 정규화된 mnemonic
    }
    static class MethodBytecode {
        String owner, name, desc;
        List<Insn> insns = new ArrayList<Insn>();                 // index-순
        Map<Integer, List<Integer>> edges = new HashMap<Integer, List<Integer>>(); // idx -> succ idx
        List<int[]> exceptionHandlers = new ArrayList<int[]>();   // [startIdx,endIdx,handlerIdx]
    }

    private static byte[] loadClassBytes(String className) throws IOException {
        String resource = "/" + className.replace('.', '/') + ".class";
        InputStream in = ByteTokAnalyzer.class.getResourceAsStream(resource);
        if (in == null) {
            // fall back: 파일로도 시도
            Path p = Paths.get("target", "classes", className.replace('.', File.separatorChar) + ".class");
            if (Files.exists(p)) return Files.readAllBytes(p);
            return null;
        }
        ByteArrayOutputStream bos = new ByteArrayOutputStream();
        byte[] buf = new byte[8192];
        int r;
        while ((r = in.read(buf)) > 0) bos.write(buf, 0, r);
        in.close();
        return bos.toByteArray();
    }

    public static List<MethodBytecode> readClass(byte[] bytes) {
        final List<MethodBytecode> out = new ArrayList<MethodBytecode>();
        ClassReader cr = new ClassReader(bytes);

        cr.accept(new ClassVisitor(Opcodes.ASM9) {
            String owner;
            @Override public void visit(int version, int access, String name, String sig, String superName, String[] interfaces) {
                owner = name.replace('/', '.');
            }
            @Override public MethodVisitor visitMethod(int access, String name, String desc, String sig, String[] exceptions) {
                final MethodNode mn = new MethodNode(Opcodes.ASM9);
                final MethodBytecode mb = new MethodBytecode();
                mb.owner = owner; mb.name = name; mb.desc = desc;
                out.add(mb);

                return new MethodVisitor(Opcodes.ASM9, mn) {
                    @Override public void visitEnd() {
                        // 인스트럭션 인덱스 매핑
                        Map<AbstractInsnNode, Integer> indexMap = new IdentityHashMap<AbstractInsnNode, Integer>();
                        int idx = 0;
                        int currentLine = -1;

                        for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                            if (ain instanceof LineNumberNode) {
                                currentLine = ((LineNumberNode) ain).line;
                            }
                            if (ain.getType() == AbstractInsnNode.LABEL
                                    || ain.getType() == AbstractInsnNode.FRAME) {
                                continue;
                            }
                            // 유효 인스트럭션
                            Insn insn = new Insn();
                            insn.index = idx;
                            insn.line = currentLine;
                            insn.mnemonic = normalizeAin(ain);
                            mb.insns.add(insn);
                            indexMap.put(ain, idx);
                            idx++;
                        }

                        // 예외 핸들러 범위: [startIdx, endIdx, handlerIdx]
                        for (TryCatchBlockNode tcb : (List<TryCatchBlockNode>) mn.tryCatchBlocks) {
                            Integer s = firstIndexOf(mn.instructions, indexMap, tcb.start);
                            Integer e = firstIndexOf(mn.instructions, indexMap, tcb.end);
                            Integer h = firstIndexOf(mn.instructions, indexMap, tcb.handler);
                            if (s != null && e != null && h != null) {
                                mb.exceptionHandlers.add(new int[]{s, e, h});
                            }
                        }

                        // CFG edges
                        for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                            if (!indexMap.containsKey(ain)) continue;
                            int from = indexMap.get(ain);
                            List<Integer> succ = mb.edges.get(from);
                            if (succ == null) { succ = new ArrayList<Integer>(); mb.edges.put(from, succ); }

                            int op = ain.getOpcode();
                            // fall-through (다음 유효 인스트럭션)
                            AbstractInsnNode nxt = ain.getNext();
                            while (nxt != null && !indexMap.containsKey(nxt)) nxt = nxt.getNext();
                            if (nxt != null && !isUnconditional(op)) {
                                succ.add(indexMap.get(nxt));
                            }

                            if (ain instanceof JumpInsnNode) {
                                LabelNode target = ((JumpInsnNode) ain).label;
                                Integer to = firstIndexOf(mn.instructions, indexMap, target);
                                if (to != null) succ.add(to);
                            } else if (ain instanceof TableSwitchInsnNode) {
                                TableSwitchInsnNode ts = (TableSwitchInsnNode) ain;
                                Integer d = firstIndexOf(mn.instructions, indexMap, ts.dflt);
                                if (d != null) succ.add(d);
                                for (LabelNode ln : (List<LabelNode>) ts.labels) {
                                    Integer to = firstIndexOf(mn.instructions, indexMap, ln);
                                    if (to != null) succ.add(to);
                                }
                            } else if (ain instanceof LookupSwitchInsnNode) {
                                LookupSwitchInsnNode ls = (LookupSwitchInsnNode) ain;
                                Integer d = firstIndexOf(mn.instructions, indexMap, ls.dflt);
                                if (d != null) succ.add(d);
                                for (LabelNode ln : (List<LabelNode>) ls.labels) {
                                    Integer to = firstIndexOf(mn.instructions, indexMap, ln);
                                    if (to != null) succ.add(to);
                                }
                            }
                        }
                    }
                };
            }
        }, ClassReader.SKIP_DEBUG /* 라인 정보가 있으면 visitLineNumber로 수집됨 */);

        return out;
    }

    private static Integer firstIndexOf(InsnList insns, Map<AbstractInsnNode,Integer> indexMap, LabelNode ln) {
        // 라벨 다음의 첫 유효 인스트럭션을 찾는다
        AbstractInsnNode a = ln;
        while (a != null && !indexMap.containsKey(a)) a = a.getNext();
        if (a == null) return null;
        return indexMap.get(a);
    }

    private static boolean isUnconditional(int opcode) {
        return opcode == Opcodes.GOTO || opcode == Opcodes.RETURN
                || opcode == Opcodes.IRETURN || opcode == Opcodes.FRETURN
                || opcode == Opcodes.ARETURN || opcode == Opcodes.LRETURN
                || opcode == Opcodes.DRETURN || opcode == Opcodes.ATHROW;
    }

    private static String normalizeAin(AbstractInsnNode ain) {
        int op = ain.getOpcode();
        if (op < 0) return "unknown";
        String base = org.objectweb.asm.util.Printer.OPCODES[op].toLowerCase();

        if (ain instanceof VarInsnNode) {
            int var = ((VarInsnNode)ain).var;
            if ((base.equals("iload") || base.equals("aload") || base.equals("fload") ||
                    base.equals("dload") || base.equals("lload") || base.equals("istore") ||
                    base.equals("fstore") || base.equals("dstore") || base.equals("lstore") ||
                    base.equals("astore")) && var >=0 && var <=3) {
                return base + "_" + var;
            }
        }
        if (ain instanceof LdcInsnNode) {
            Object c = ((LdcInsnNode)ain).cst;
            if (c instanceof Float) {
                float v = ((Float)c).floatValue();
                if (v == 0f) return "fconst_0";
                if (v == 1f) return "fconst_1";
                if (v == 2f) return "fconst_2";
                return "ldc";
            }
            if (c instanceof Integer) {
                Integer iv = (Integer)c;
                switch (iv) {
                    case -1: return "iconst_m1";
                    case 0: return "iconst_0";
                    case 1: return "iconst_1";
                    case 2: return "iconst_2";
                    case 3: return "iconst_3";
                    case 4: return "iconst_4";
                    case 5: return "iconst_5";
                }
            }
        }
        return base;
    }
}