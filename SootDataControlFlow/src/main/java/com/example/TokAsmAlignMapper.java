package com.example;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

/**
 * 하나의 완성된 그래프(JSON) 생성기:
 * - ASM 기준 노드/에지(CFG) 생성
 * - ByteTok 정렬 결과로 byte_index/size/hex 병합
 * - 단일 그래프(JSON)만 출력
 */
public class TokAsmAlignMapper {

    public static void main(String[] args) throws Exception {
        // 입력 경로 설정 (args 우선, 없으면 기본값)
        String classPath = (args != null && args.length >= 1)
                ? args[0]
                : "src/main/resources/edu/handong/csee/isel/machinelearning/DNN_node.class";
        String btokPath  = (args != null && args.length >= 2)
                ? args[1]
                : "src/main/resources/bytetok.txt";

        byte[] bytes = loadClassBytes(classPath);
        if (bytes == null) {
            System.err.println("[ERROR] Cannot load class: " + classPath);
            return;
        }

        List<MethodBC> bcMethods = AsmUtil.readClass(bytes);
        ByteTokFile btok = parseByteTokByMethod(btokPath);

        Gson gson = new GsonBuilder().setPrettyPrinting().create();
        Files.createDirectories(Paths.get("output"));

        int mcount = Math.min(bcMethods.size(), btok.methods.size());
        System.out.printf("→ Methods (ASM=%d, TOK=%d) -> processing %d%n",
                bcMethods.size(), btok.methods.size(), mcount);

        for (int m = 0; m < mcount; m++) {
            MethodBC mb = bcMethods.get(m);
            ByteTokMethod tm = btok.methods.get(m);

            AlignResult ar = align(mb, tm);

            // ByteTok → ASM 노드로 바이트 정보(오프셋/길이/hex)를 전파(병합)
            for (int ti = 0; ti < ar.tokToAsm.length; ti++) {
                int ai = ar.tokToAsm[ti];
                if (ai >= 0) {
                    MethodBC.BCInsn bi = mb.insns.get(ai);
                    ByteTokEntry be = tm.entries.get(ti);
                    bi.byteIndex = be.byteIndex;
                    bi.size = be.size;
                    bi.hex = be.opcodeHex;
                }
            }

            // 단일 그래프(JSON) 구성
            Map<String, Object> graph = new LinkedHashMap<>();
            List<Map<String, Object>> nodes = new ArrayList<>();
            for (MethodBC.BCInsn bi : mb.insns) {
                Map<String, Object> n = new LinkedHashMap<>();
                n.put("id", bi.index);               // 0..N-1
                n.put("mnemonic", bi.mnemonic);      // ASM 기준 정규화된 mnemonic
                n.put("byte_index", bi.byteIndex);   // -1: 매칭 실패
                n.put("size", bi.size);              // -1: 매칭 실패
                n.put("hex", bi.hex);                // null: 매칭 실패
                nodes.add(n);
            }
            List<int[]> edges = new ArrayList<>();
            for (Map.Entry<Integer, List<Integer>> e : mb.edges.entrySet()) {
                int from = e.getKey();
                for (Integer to : e.getValue()) edges.add(new int[]{from, to});
            }
            graph.put("nodes", nodes);
            graph.put("edges", edges);

            // 토큰 기반 메서드 바이트 총 길이
            int methodCodeSize = tm.entries.isEmpty()
                    ? 0
                    : tm.entries.get(tm.entries.size() - 1).byteIndex + tm.entries.get(tm.entries.size() - 1).size;

            Map<String, Object> out = new LinkedHashMap<>();
            out.put("graph", graph);
            out.put("method_code_size", methodCodeSize);
            out.put("align_score", ar.score);

            String fileName = "graph_" + sanitize(mb.name) + ".json";
            Path p = Paths.get("output", fileName);
            Files.write(p, gson.toJson(out).getBytes("UTF-8"));
            System.out.println("✅ Saved " + p.toAbsolutePath());
        }
    }

    static String sanitize(String s) { return s.replaceAll("[^a-zA-Z0-9_]", "_"); }

    // ===== ASM 수집(라벨 null-safe, CFG 생성) =====
    static class MethodBC {
        String owner, name, desc;
        static class BCInsn {
            int index;          // ASM 인스트럭션 순번
            int line;           // 소스 라인(출력엔 포함 안 함)
            int byteIndex = -1; // ByteTok 매칭 시 바이트 오프셋, 없으면 -1
            int size = -1;      // 매칭 시 바이트 길이, 없으면 -1
            String hex = null;  // 매칭 시 원시 hex, 없으면 null
            String mnemonic;    // 정규화된 ASM mnemonic
        }
        List<BCInsn> insns = new ArrayList<>();
        Map<Integer, List<Integer>> edges = new HashMap<>();
    }

    static class AsmUtil {
        static List<MethodBC> readClass(byte[] bytes) {
            final List<MethodBC> out = new ArrayList<>();
            ClassReader cr = new ClassReader(bytes);
            cr.accept(new ClassVisitor(Opcodes.ASM9) {
                String owner;
                @Override
                public void visit(int version, int access, String name, String sig, String superName, String[] interfaces) {
                    owner = name.replace('/', '.');
                }
                @Override
                public MethodVisitor visitMethod(int access, String name, String desc, String sig, String[] exceptions) {
                    final MethodNode mn = new MethodNode(Opcodes.ASM9);
                    final MethodBC mb = new MethodBC();
                    mb.owner = owner; mb.name = name; mb.desc = desc;
                    out.add(mb);
                    return new MethodVisitor(Opcodes.ASM9, mn) {
                        @Override
                        public void visitEnd() {
                            Map<AbstractInsnNode, Integer> indexMap = new IdentityHashMap<>();
                            int idx = 0, currentLine = -1;

                            // 1) 인스트럭션 수집 (LABEL/FRAME/LINE 제외), 인덱스 부여
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (ain instanceof LineNumberNode) { currentLine = ((LineNumberNode) ain).line; continue; }
                                if (ain.getType() == AbstractInsnNode.LABEL || ain.getType() == AbstractInsnNode.FRAME) continue;

                                MethodBC.BCInsn bi = new MethodBC.BCInsn();
                                bi.index = idx;
                                bi.line = currentLine;
                                bi.mnemonic = normalize(ain);
                                mb.insns.add(bi);
                                indexMap.put(ain, idx);
                                idx++;
                            }

                            // 2) CFG 에지 구성
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (!indexMap.containsKey(ain)) continue;
                                int from = indexMap.get(ain);
                                List<Integer> succ = mb.edges.computeIfAbsent(from, k -> new ArrayList<>());

                                int op = ain.getOpcode();
                                // fall-through
                                AbstractInsnNode nxt = ain.getNext();
                                while (nxt != null && !indexMap.containsKey(nxt)) nxt = nxt.getNext();
                                if (nxt != null && !isUncond(op)) succ.add(indexMap.get(nxt));

                                // explicit branch
                                if (ain instanceof JumpInsnNode) {
                                    Integer to = firstIndexOfSafe(mn.instructions, indexMap, ((JumpInsnNode) ain).label);
                                    if (to != null) succ.add(to);
                                } else if (ain instanceof TableSwitchInsnNode) {
                                    TableSwitchInsnNode ts = (TableSwitchInsnNode) ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ts.dflt);
                                    if (d != null) succ.add(d);
                                    for (LabelNode l : ts.labels) {
                                        Integer to = firstIndexOfSafe(mn.instructions, indexMap, l);
                                        if (to != null) succ.add(to);
                                    }
                                } else if (ain instanceof LookupSwitchInsnNode) {
                                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode) ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ls.dflt);
                                    if (d != null) succ.add(d);
                                    for (LabelNode l : ls.labels) {
                                        Integer to = firstIndexOfSafe(mn.instructions, indexMap, l);
                                        if (to != null) succ.add(to);
                                    }
                                }
                            }
                        }
                    };
                }
            }, 0);
            return out;
        }

        static boolean isUncond(int opcode) {
            return opcode == Opcodes.GOTO || opcode == Opcodes.RETURN
                    || opcode == Opcodes.IRETURN || opcode == Opcodes.FRETURN
                    || opcode == Opcodes.ARETURN || opcode == Opcodes.LRETURN
                    || opcode == Opcodes.DRETURN || opcode == Opcodes.ATHROW;
        }

        static Integer firstIndexOfSafe(InsnList insns, Map<AbstractInsnNode, Integer> map, LabelNode ln) {
            if (ln == null) return null;
            AbstractInsnNode a = ln;
            while (a != null && !map.containsKey(a)) a = a.getNext();
            return (a == null) ? null : map.get(a);
        }

        static String normalize(AbstractInsnNode ain) {
            int op = ain.getOpcode();
            if (op < 0) return "unknown";
            String base = org.objectweb.asm.util.Printer.OPCODES[op].toLowerCase();

            // var load/store 단축형 정규화 (xload_n / xstore_n)
            if (ain instanceof VarInsnNode) {
                int v = ((VarInsnNode) ain).var;
                if ((base.endsWith("load") || base.endsWith("store")) && v >= 0 && v <= 3) {
                    return base + "_" + v;
                }
            }
            if (ain instanceof LdcInsnNode) {
                Object c = ((LdcInsnNode) ain).cst;
                if (c instanceof Float) {
                    float f = (Float) c;
                    if (f == 0f) return "fconst_0";
                    if (f == 1f) return "fconst_1";
                    if (f == 2f) return "fconst_2";
                }
                if (c instanceof Integer) {
                    int iv = (Integer) c;
                    switch (iv) {
                        case -1: return "iconst_m1";
                        case 0:  return "iconst_0";
                        case 1:  return "iconst_1";
                        case 2:  return "iconst_2";
                        case 3:  return "iconst_3";
                        case 4:  return "iconst_4";
                        case 5:  return "iconst_5";
                    }
                }
            }
            return base;
        }
    }

    // ===== ByteTok 파서(바이트 오프셋 계산 포함) =====
    static class ByteTokEntry {
        int index;            // 토큰 인덱스(메서드 내)
        String instrName;     // 정규화된 이름
        String opcodeHex;     // 바이트코드 hex (공백 제거)
        String rawLine;       // 원본 라인(출력에는 사용 안 함)
        int byteIndex;        // 메서드 코드 내 시작 바이트 오프셋
        int size;             // 이 인스트럭션의 바이트 수
    }
    static class ByteTokMethod { String methodIdLine; List<ByteTokEntry> entries = new ArrayList<>(); }
    static class ByteTokFile { List<ByteTokMethod> methods = new ArrayList<>(); }

    static ByteTokFile parseByteTokByMethod(String path) throws IOException {
        List<String> lines = Files.readAllLines(Paths.get(path));
        ByteTokFile out = new ByteTokFile();
        ByteTokMethod cur = null; int localIdx = 0; int curByteIndex = 0;

        for (String raw : lines) {
            String t = raw.trim();
            if (t.startsWith("Method:")) {
                cur = new ByteTokMethod();
                cur.methodIdLine = t;
                out.methods.add(cur);
                localIdx = 0;
                curByteIndex = 0;  // 메서드 시작 시 오프셋 리셋
                continue;
            }
            if (cur == null) continue;

            if (t.startsWith("- ") && t.toLowerCase().contains(" instruction:")) {
                String[] parts = t.split("instruction:");
                if (parts.length < 2) continue;
                String nameRaw = parts[0].substring(2).trim();
                String hex = parts[1].trim().toUpperCase().replaceAll("\\s+","");
                String norm = normalizeTok(nameRaw, hex);

                ByteTokEntry e = new ByteTokEntry();
                e.index = localIdx++;
                e.instrName = norm;
                e.opcodeHex = hex;
                e.rawLine = t;

                e.size = hexLen(hex);
                e.byteIndex = curByteIndex;
                curByteIndex += e.size;

                cur.entries.add(e);
            }
        }
        return out;
    }

    static int hexLen(String hex) {
        String cleaned = (hex == null) ? "" : hex.replaceAll("[^0-9A-Fa-f]", "");
        return cleaned.length() / 2;
    }

    static String normalizeTok(String nameRaw, String hex) {
        String n = (nameRaw == null ? "" : nameRaw).toLowerCase();

        if (n.equals("aload_n")) return indexFrom(hex, "aload");
        if (n.equals("iload_n")) return indexFrom(hex, "iload");
        if (n.equals("fload_n")) return indexFrom(hex, "fload");
        if (n.equals("dload_n")) return indexFrom(hex, "dload");
        if (n.equals("lload_n")) return indexFrom(hex, "lload");
        if (n.equals("istore_n")) return indexFrom(hex, "istore");
        if (n.equals("fstore_n")) return indexFrom(hex, "fstore");

        if (n.equals("i_const") || n.equals("iconst")) {
            if (hex != null && hex.toUpperCase().startsWith("02")) return "iconst_m1";
            if (hex != null && hex.toUpperCase().startsWith("03")) return "iconst_0";
            if (hex != null && hex.toUpperCase().startsWith("04")) return "iconst_1";
            if (hex != null && hex.toUpperCase().startsWith("05")) return "iconst_2";
            if (hex != null && hex.toUpperCase().startsWith("06")) return "iconst_3";
            if (hex != null && hex.toUpperCase().startsWith("07")) return "iconst_4";
            if (hex != null && hex.toUpperCase().startsWith("08")) return "iconst_5";
            return "iconst";
        }
        if (n.equals("f_const") || n.equals("fconst")) {
            if (hex != null && hex.toUpperCase().startsWith("0B")) return "fconst_0";
            if (hex != null && hex.toUpperCase().startsWith("0C")) return "fconst_1";
            if (hex != null && hex.toUpperCase().startsWith("0D")) return "fconst_2";
            return "fconst";
        }

        if (n.equals("f_return")) return "freturn";
        if (n.equals("d_return")) return "dreturn";
        if (n.equals("i_return")) return "ireturn";
        if (n.equals("a_return")) return "areturn";
        if (n.equals("l_return")) return "lreturn";

        return n;
    }

    static String indexFrom(String hex, String base) {
        try {
            int op = Integer.parseInt(hex.substring(0, 2), 16);
            if ("aload".equals(base) && op >= 0x2A && op <= 0x2D) return "aload_" + (op - 0x2A);
            if ("iload".equals(base) && op >= 0x1A && op <= 0x1D) return "iload_" + (op - 0x1A);
            if ("fload".equals(base) && op >= 0x22 && op <= 0x25) return "fload_" + (op - 0x22);
            if ("dload".equals(base) && op >= 0x26 && op <= 0x29) return "dload_" + (op - 0x26);
            if ("lload".equals(base) && op >= 0x1E && op <= 0x21) return "lload_" + (op - 0x1E);
            if ("istore".equals(base) && op >= 0x3B && op <= 0x3E) return "istore_" + (op - 0x3B);
            if ("fstore".equals(base) && op >= 0x43 && op <= 0x46) return "fstore_" + (op - 0x43);
        } catch (Exception ignore) {}
        return base;
    }

    // ===== 단순 글로벌 정렬 (토큰 vs ASM mnemonic)
    static class AlignResult { int[] tokToAsm; int[] asmToTok; int score; }

    static AlignResult align(MethodBC mb, ByteTokMethod tm) {
        List<String> A = new ArrayList<>(); // ASM
        for (MethodBC.BCInsn bi : mb.insns) A.add(bi.mnemonic);

        List<String> B = new ArrayList<>(); // TOK
        for (ByteTokEntry be : tm.entries) B.add(be.instrName);

        int n = B.size(), m = A.size();
        int[][] dp = new int[n + 1][m + 1];
        int MATCH = 2, MISMATCH = -1, GAP = -1;

        for (int i = 1; i <= n; i++) dp[i][0] = dp[i - 1][0] + GAP;
        for (int j = 1; j <= m; j++) dp[0][j] = dp[0][j - 1] + GAP;

        for (int i = 1; i <= n; i++) {
            String bt = B.get(i - 1);
            for (int j = 1; j <= m; j++) {
                String aa = A.get(j - 1);
                int s = score(bt, aa, MATCH, MISMATCH);
                dp[i][j] = max3(dp[i - 1][j - 1] + s, dp[i - 1][j] + GAP, dp[i][j - 1] + GAP);
            }
        }

        int i = n, j = m;
        int[] tokToAsm = new int[n]; Arrays.fill(tokToAsm, -1);
        int[] asmToTok = new int[m]; Arrays.fill(asmToTok, -1);

        while (i > 0 || j > 0) {
            if (i > 0 && j > 0 && dp[i][j] == dp[i - 1][j - 1] + score(B.get(i - 1), A.get(j - 1), MATCH, MISMATCH)) {
                if (isMatch(B.get(i - 1), A.get(j - 1))) {
                    tokToAsm[i - 1] = j - 1;
                    asmToTok[j - 1] = i - 1;
                }
                i--; j--;
            } else if (i > 0 && dp[i][j] == dp[i - 1][j] + GAP) {
                i--;
            } else {
                j--;
            }
        }
        AlignResult ar = new AlignResult();
        ar.tokToAsm = tokToAsm; ar.asmToTok = asmToTok; ar.score = dp[n][m];
        return ar;
    }

    static int score(String t, String a, int MATCH, int MISMATCH) { return isMatch(t, a) ? MATCH : MISMATCH; }
    static boolean isMatch(String t, String a) { return t.equals(a) || t.startsWith(a) || a.startsWith(t); }
    static int max3(int a, int b, int c) { return Math.max(a, Math.max(b, c)); }

    // ===== IO =====
    static byte[] loadClassBytes(String classNameOrPath) throws IOException {
        Path p = Paths.get(classNameOrPath);
        if (!Files.exists(p)) throw new FileNotFoundException("Class file not found: " + p.toAbsolutePath());
        return Files.readAllBytes(p);
    }
}