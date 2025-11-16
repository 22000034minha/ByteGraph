package com.example;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

public class AsmBytecodeGraph {

    public static void main(String[] args) throws Exception {
        // ★ 파일 경로 그대로 사용
        String className = "src/main/resources/edu/handong/csee/isel/machinelearning/DNN_node.class";

        byte[] bytes = loadClassBytes(className);
        if (bytes == null) {
            System.err.println("[ERROR] Cannot load class bytes for " + className);
            return;
        }
        List<MethodBytecode> methods = readClass(bytes);

        Gson gson = new GsonBuilder().setPrettyPrinting().create();
        Files.createDirectories(Paths.get("output"));

        for (MethodBytecode mb : methods) {
            Map<String,Object> out = new LinkedHashMap<>();
            List<Map<String,Object>> nodes = new ArrayList<>();
            List<int[]> edgesArr = new ArrayList<>();

            for (int i = 0; i < mb.insns.size(); i++) {
                Insn insn = mb.insns.get(i);
                Map<String,Object> n = new LinkedHashMap<>();
                n.put("idx", insn.index);
                n.put("mnemonic", insn.mnemonic);
                n.put("line", insn.line);
                nodes.add(n);
            }
            for (Map.Entry<Integer, List<Integer>> e : mb.edges.entrySet()) {
                int from = e.getKey();
                for (Integer to : e.getValue()) edgesArr.add(new int[]{from, to});
            }

            out.put("owner", mb.owner);
            out.put("name", mb.name);
            out.put("desc", mb.desc);
            out.put("nodes", nodes);
            out.put("edges", edgesArr);
            out.put("exceptions", mb.exceptionHandlers);

            String safe = mb.name.replaceAll("[^a-zA-Z0-9_]", "_");
            Path p = Paths.get("output", "bytecode_graph_" + safe + ".json");
            Files.write(p, gson.toJson(out).getBytes("UTF-8"));
            System.out.println("✅ Saved " + p.toAbsolutePath());
        }
    }

    // ===== ASM 수집 =====
    static class Insn { int index; int line; String mnemonic; }
    static class MethodBytecode {
        String owner, name, desc;
        List<Insn> insns = new ArrayList<>();
        Map<Integer, List<Integer>> edges = new HashMap<>();
        List<int[]> exceptionHandlers = new ArrayList<>();
    }

    private static byte[] loadClassBytes(String classNameOrPath) throws IOException {
        // 파일 경로 직접 처리
        if (classNameOrPath.endsWith(".class") || classNameOrPath.contains("/") || classNameOrPath.contains("\\")) {
            Path p = Paths.get(classNameOrPath);
            if (!Files.exists(p)) throw new FileNotFoundException("Class file not found: " + p.toAbsolutePath());
            return Files.readAllBytes(p);
        }
        // 바이너리 이름으로 들어온 경우(예비)
        String resource = "/" + classNameOrPath.replace('.', '/') + ".class";
        InputStream in = AsmBytecodeGraph.class.getResourceAsStream(resource);
        if (in != null) {
            ByteArrayOutputStream bos = new ByteArrayOutputStream();
            byte[] buf = new byte[8192]; int r;
            while ((r = in.read(buf)) > 0) bos.write(buf, 0, r);
            in.close();
            return bos.toByteArray();
        }
        Path p = Paths.get("target", "classes", classNameOrPath.replace('.', File.separatorChar) + ".class");
        if (Files.exists(p)) return Files.readAllBytes(p);
        throw new FileNotFoundException("Cannot load class bytes for " + classNameOrPath);
    }

    public static List<MethodBytecode> readClass(byte[] bytes) {
        final List<MethodBytecode> out = new ArrayList<>();
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
                        Map<AbstractInsnNode, Integer> indexMap = new IdentityHashMap<>();
                        int idx = 0, currentLine = -1;

                        for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                            if (ain instanceof LineNumberNode) { currentLine = ((LineNumberNode) ain).line; continue; }
                            if (ain.getType() == AbstractInsnNode.LABEL || ain.getType() == AbstractInsnNode.FRAME) continue;
                            Insn bi = new Insn();
                            bi.index = idx; bi.line = currentLine; bi.mnemonic = normalize(ain);
                            mb.insns.add(bi);
                            indexMap.put(ain, idx);
                            idx++;
                        }

                        // 예외 핸들러 (null-safe)
                        if (mn.tryCatchBlocks != null) {
                            for (TryCatchBlockNode tcb : mn.tryCatchBlocks) {
                                Integer s = firstIndexOfSafe(mn.instructions, indexMap, tcb.start);
                                Integer e = firstIndexOfSafe(mn.instructions, indexMap, tcb.end);
                                Integer h = firstIndexOfSafe(mn.instructions, indexMap, tcb.handler);
                                if (s != null && e != null && h != null) mb.exceptionHandlers.add(new int[]{s, e, h});
                            }
                        }

                        // CFG 엣지
                        for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                            Integer from = indexMap.get(ain);
                            if (from == null) continue;
                            List<Integer> succ = mb.edges.computeIfAbsent(from, k -> new ArrayList<>());

                            int op = ain.getOpcode();
                            AbstractInsnNode nxt = ain.getNext();
                            while (nxt != null && !indexMap.containsKey(nxt)) nxt = nxt.getNext();
                            if (nxt != null && !isUncond(op)) succ.add(indexMap.get(nxt));

                            if (ain instanceof JumpInsnNode) {
                                Integer to = firstIndexOfSafe(mn.instructions, indexMap, ((JumpInsnNode) ain).label);
                                if (to != null) succ.add(to);
                            } else if (ain instanceof TableSwitchInsnNode) {
                                TableSwitchInsnNode ts = (TableSwitchInsnNode) ain;
                                Integer d = firstIndexOfSafe(mn.instructions, indexMap, ts.dflt);
                                if (d != null) succ.add(d);
                                for (LabelNode ln : ts.labels) {
                                    Integer to = firstIndexOfSafe(mn.instructions, indexMap, ln);
                                    if (to != null) succ.add(to);
                                }
                            } else if (ain instanceof LookupSwitchInsnNode) {
                                LookupSwitchInsnNode ls = (LookupSwitchInsnNode) ain;
                                Integer d = firstIndexOfSafe(mn.instructions, indexMap, ls.dflt);
                                if (d != null) succ.add(d);
                                for (LabelNode ln : ls.labels) {
                                    Integer to = firstIndexOfSafe(mn.instructions, indexMap, ln);
                                    if (to != null) succ.add(to);
                                }
                            }
                        }
                    }
                };
            }
        }, 0 /* 라인/프레임 유지 */);
        return out;
    }

    private static Integer firstIndexOfSafe(InsnList insns, Map<AbstractInsnNode,Integer> indexMap, LabelNode ln) {
        if (ln == null) return null;
        AbstractInsnNode a = ln;
        while (a != null && !indexMap.containsKey(a)) a = a.getNext();
        return (a == null) ? null : indexMap.get(a);
    }

    private static boolean isUncond(int opcode) {
        return opcode == Opcodes.GOTO || opcode == Opcodes.RETURN
                || opcode == Opcodes.IRETURN || opcode == Opcodes.FRETURN
                || opcode == Opcodes.ARETURN || opcode == Opcodes.LRETURN
                || opcode == Opcodes.DRETURN || opcode == Opcodes.ATHROW;
    }

    private static String normalize(AbstractInsnNode ain) {
        int op = ain.getOpcode();
        if (op < 0) return "unknown";
        String base = org.objectweb.asm.util.Printer.OPCODES[op].toLowerCase();
        if (ain instanceof VarInsnNode) {
            int var = ((VarInsnNode)ain).var;
            if ((base.endsWith("load") || base.endsWith("store")) && var>=0 && var<=3) return base + "_" + var;
        }
        if (ain instanceof LdcInsnNode) {
            Object c = ((LdcInsnNode)ain).cst;
            if (c instanceof Float) {
                float f = ((Float)c);
                if (f==0f) return "fconst_0"; if (f==1f) return "fconst_1"; if (f==2f) return "fconst_2";
            }
            if (c instanceof Integer) {
                int iv = ((Integer)c);
                switch (iv) { case -1:return "iconst_m1"; case 0:return "iconst_0"; case 1:return "iconst_1";
                    case 2:return "iconst_2"; case 3:return "iconst_3"; case 4:return "iconst_4"; case 5:return "iconst_5"; }
            }
        }
        return base;
    }
}