package com.example;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import soot.*;
import soot.options.Options;
import soot.tagkit.SourceLineNumberTag;
import soot.tagkit.LineNumberTag;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

/**
 * 하나의 완전한 그래프(JSON) 생성기:
 * - ASM으로 CFG 생성
 * - ByteTok 정렬 결과로 ASM 노드에 byte_index / size / hex 병합
 * - Soot(Jimple)는 로딩/매칭에만 사용 가능(출력에는 포함하지 않음). Soot 실패해도 ASM-only로 진행.
 *
 * 출력 예:
 * {
 *   "graph": { "nodes":[{"id":0,"mnemonic":"iload_0","byte_index":0,"size":1,"hex":"1A"}, ...],
 *              "edges":[[0,1],[1,2], ...] },
 *   "method_code_size": 42,
 *   "align_score": 123
 * }
 */
public class AsmSootAnchoredMapper {

    public static void main(String[] args) throws Exception {
        // ---- 입력 설정 ----
        String classPath = (args != null && args.length >= 1 && args[0] != null && !args[0].trim().isEmpty())
                ? args[0].trim()
                : "src/main/resources/edu/handong/csee/isel/machinelearning/DNN_node.class";
        String btokPath  = (args != null && args.length >= 2 && args[1] != null && !args[1].trim().isEmpty())
                ? args[1].trim()
                : "src/main/resources/bytetok.txt";

        Path classFile = Paths.get(classPath).toAbsolutePath();
        System.out.println("[INFO] Class file: " + classFile);
        if (!Files.exists(classFile)) {
            System.err.println("[ERROR] Class file not found: " + classFile);
            return;
        }

        // ---- ASM: .class 파싱 ----
        byte[] bytes = Files.readAllBytes(classFile);
        List<MethodBC> bcMethods = AsmUtil.readClass(bytes);
        System.out.println("[INFO] ASM methods: " + bcMethods.size());
        for (MethodBC mb : bcMethods) {
            System.out.println("  - " + mb.name + " " + mb.desc + " (insns=" + mb.insns.size() + ")");
        }

        // ---- classpath root / binary name 탐지 ----
        Path classpathRoot = detectClasspathRoot(classFile);
        String binaryName  = toBinaryNameFromPath(classFile, classpathRoot);
        System.out.println("[INFO] classpathRoot=" + classpathRoot);
        System.out.println("[INFO] binaryName=" + binaryName);

        // ---- Soot 로딩 (선택적) ----
        SootClass sc = null;
        List<SootMethod> sootConcrete = new ArrayList<>();
        try {
            sc = initSootAndLoad(binaryName, classpathRoot.toString());
            for (SootMethod sm : sc.getMethods()) if (sm.isConcrete()) sootConcrete.add(sm);
            System.out.println("[INFO] Soot concrete methods: " + sootConcrete.size());
            for (SootMethod sm : sootConcrete) System.out.println("  - " + sm.getSignature());
        } catch (Throwable t) {
            System.err.println("[WARN] Soot load failed: " + t.getMessage());
        }

        // ---- ByteTok 파싱 (바이트 오프셋 포함) ----
        ByteTokFile btok = parseByteTokByMethod(btokPath);
        System.out.println("[INFO] ByteTok methods parsed: " + btok.methods.size());

        Files.createDirectories(Paths.get("output"));
        final Gson gson = new GsonBuilder().setPrettyPrinting().create();

        // ASM 메서드 색인 (이름 → 후보들)
        Map<String, List<MethodBC>> asmIndex = indexAsmByName(bcMethods);

        // ByteTok 메서드 키 색인(가능하면)
        Map<MethodKey, ByteTokMethod> btokByKey = indexBtokByMethodKey(btok);

        // ---- 처리: Soot 성공 → Soot concrete 기준, 실패 → ASM 기준 ----
        if (sc != null && !sootConcrete.isEmpty()) {
            for (SootMethod sm : sootConcrete) {
                MethodBC mb = findAsmMethodForSoot(sm, asmIndex);
                if (mb == null) {
                    System.err.println("[WARN] No ASM method matched for " + sm.getSignature() + ". Skipped.");
                    continue;
                }
                // ByteTok 선택(시그니처 우선, 폴백: 점수 최대)
                MatchResult match = selectTokForAsm(mb, btok, btokByKey);
                emitSingleGraphJson(mb, match, gson, binaryName);
            }
        } else {
            // Soot 실패 또는 concrete=0 → ASM 메서드 순회
            for (MethodBC mb : bcMethods) {
                MatchResult match = selectTokForAsm(mb, btok, btokByKey);
                emitSingleGraphJson(mb, match, gson, binaryName);
            }
        }

        System.out.println("[INFO] Done.");
    }

    // =========================================
    // 단일 그래프 JSON 생성
    // =========================================
    private static void emitSingleGraphJson(MethodBC mb, MatchResult match, Gson gson, String binaryName) throws IOException {
        // 1) 정렬이 존재하면 ByteTok → ASM 노드에 바이트 정보 병합
        int alignScore = 0;
        int methodCodeSize = 0;
        if (match != null && match.tm != null && match.ar != null) {
            // ASM 각 노드에 기본값
            for (MethodBC.BCInsn bi : mb.insns) {
                bi.byteIndex = -1; bi.size = -1; bi.hex = null;
            }
            for (int ti = 0; ti < match.ar.tokToAsm.length; ti++) {
                int ai = match.ar.tokToAsm[ti];
                if (ai >= 0) {
                    MethodBC.BCInsn bi = mb.insns.get(ai);
                    ByteTokEntry be = match.tm.entries.get(ti);
                    bi.byteIndex = be.byteIndex;
                    bi.size = be.size;
                    bi.hex = be.opcodeHex;
                }
            }
            alignScore = match.ar.score;
            methodCodeSize = match.tm.entries.isEmpty()
                    ? 0
                    : match.tm.entries.get(match.tm.entries.size()-1).byteIndex
                    + match.tm.entries.get(match.tm.entries.size()-1).size;
        } else {
            // 정렬 실패 시 기본값 유지(-1/null)
            alignScore = 0;
            methodCodeSize = 0;
        }

        // 2) 단일 그래프 구성
        Map<String, Object> graph = new LinkedHashMap<>();
        List<Map<String, Object>> nodes = new ArrayList<>();
        for (MethodBC.BCInsn bi : mb.insns) {
            Map<String, Object> n = new LinkedHashMap<>();
            n.put("id", bi.index);
            n.put("mnemonic", bi.mnemonic);
            n.put("byte_index", bi.byteIndex);
            n.put("size", bi.size);
            n.put("hex", bi.hex);
            // 정말 슬림하게 하려면 mnemonic/hex/size 제거 가능
            nodes.add(n);
        }
        List<int[]> edges = new ArrayList<>();
        for (Map.Entry<Integer, List<Integer>> e : mb.edges.entrySet()) {
            int from = e.getKey();
            for (Integer to : e.getValue()) edges.add(new int[]{from, to});
        }
        graph.put("nodes", nodes);
        graph.put("edges", edges);

        Map<String, Object> out = new LinkedHashMap<>();
        out.put("graph", graph);
        out.put("method_code_size", methodCodeSize);
        out.put("align_score", alignScore);

        // 파일명: binaryName + name + 오버로드 충돌 방지를 위해 desc 해시
        String methSafe = sanitize(mb.name);
        String descHash = Integer.toHexString((mb.desc == null ? "" : mb.desc).hashCode());
        String ownerSafe = (binaryName == null ? "unknown" : binaryName).replace('.', '_');
        String fileName = "graph_" + ownerSafe + "_" + methSafe + "_" + descHash + ".json";

        Path p = Paths.get("output", fileName);
        Files.write(p, gson.toJson(out).getBytes("UTF-8"));
        System.out.println("✅ Saved " + p.toAbsolutePath());
    }

    static String sanitize(String s) { return s == null ? "null" : s.replaceAll("[^a-zA-Z0-9_]", "_"); }

    // =========================================
    // 패키지 루트 자동 탐지 / 바이너리 이름 변환
    // =========================================
    private static Path detectClasspathRoot(Path classFile) {
        String s = classFile.toString().replace('\\','/');
        String[] roots = {
                "/target/classes/",
                "/build/classes/java/main/",
                "/out/production/",
                "/bin/",
                "/src/main/resources/",
                "/src/test/resources/",
                "/src/main/java/",
                "/src/test/java/"
        };
        for (String root : roots) {
            int idx = s.indexOf(root);
            if (idx >= 0) {
                String rootStr = s.substring(0, idx + root.length() - 1); // 마지막 슬래시 제거
                return Paths.get(rootStr);
            }
        }
        List<String> pkgStarts = Arrays.asList("/edu/", "/com/", "/org/", "/net/");
        int best = Integer.MAX_VALUE; String hit = null;
        for (String ps : pkgStarts) {
            int idx = s.indexOf(ps);
            if (idx >= 0 && idx < best) { best = idx; hit = ps; }
        }
        if (hit != null && best < s.length()) {
            String rootStr = s.substring(0, best);
            return Paths.get(rootStr);
        }
        return classFile.getParent().getParent() != null ? classFile.getParent().getParent() : classFile.getParent();
    }

    private static String toBinaryNameFromPath(Path classFile, Path classpathRoot) {
        String abs = classFile.toAbsolutePath().toString().replace('\\','/');
        String root = classpathRoot.toAbsolutePath().toString().replace('\\','/');
        if (!root.endsWith("/")) root += "/";
        if (abs.endsWith(".class")) abs = abs.substring(0, abs.length()-6);
        if (abs.startsWith(root)) {
            String rel = abs.substring(root.length());
            return rel.replace('/', '.'); // edu.handong....
        }
        String nameOnly = classFile.getFileName().toString();
        if (nameOnly.endsWith(".class")) nameOnly = nameOnly.substring(0, nameOnly.length()-6);
        return nameOnly; // 폴백
    }

    // =========================================
    // Soot 초기화/클래스 로딩 (선택)
    // =========================================
    private static SootClass initSootAndLoad(String binaryName, String classDir) {
        Options.v().set_prepend_classpath(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(false);
        Options.v().set_keep_line_number(true);
        Options.v().set_no_bodies_for_excluded(true);
        Options.v().set_exclude(Arrays.asList("java.", "javax.", "sun.", "com.sun.", "jdk.", "org.w3c.", "org.xml."));

        String cp = Scene.v().defaultClassPath() + File.pathSeparator + classDir;
        Options.v().set_soot_classpath(cp);
        Options.v().set_process_dir(Collections.singletonList(classDir));

        SootClass sc = Scene.v().forceResolve(binaryName, SootClass.BODIES);
        sc.setApplicationClass();
        Scene.v().loadNecessaryClasses();
        return sc;
    }

    // =========================================
    // ASM 수집 유틸 (CFG + 정규화)
    // =========================================
    static class MethodBC {
        String owner, name, desc;
        static class BCInsn {
            int index, line;
            String mnemonic;
            // ByteTok 병합 필드
            int byteIndex = -1;
            int size = -1;
            String hex = null;
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
                @Override public void visit(int version, int access, String name, String sig, String superName, String[] interfaces) {
                    owner = name.replace('/', '.');
                }
                @Override public MethodVisitor visitMethod(int access, String name, String desc, String sig, String[] exceptions) {
                    final MethodNode mn = new MethodNode(Opcodes.ASM9);
                    final MethodBC mb = new MethodBC(); mb.owner=owner; mb.name=name; mb.desc=desc; out.add(mb);
                    return new MethodVisitor(Opcodes.ASM9, mn) {
                        @Override public void visitEnd() {
                            Map<AbstractInsnNode,Integer> indexMap = new IdentityHashMap<>();
                            int idx=0, currentLine=-1;
                            // 노드 수집
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (ain instanceof LineNumberNode) { currentLine = ((LineNumberNode) ain).line; continue; }
                                if (ain.getType()==AbstractInsnNode.LABEL || ain.getType()==AbstractInsnNode.FRAME) continue;
                                MethodBC.BCInsn bi = new MethodBC.BCInsn();
                                bi.index=idx; bi.line=currentLine; bi.mnemonic=normalize(ain);
                                mb.insns.add(bi); indexMap.put(ain, idx); idx++;
                            }
                            // 에지(CFG) 수집
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (!indexMap.containsKey(ain)) continue;
                                int from = indexMap.get(ain);
                                List<Integer> succ = mb.edges.computeIfAbsent(from, k -> new ArrayList<>());
                                int op = ain.getOpcode();
                                AbstractInsnNode nxt = ain.getNext();
                                while (nxt!=null && !indexMap.containsKey(nxt)) nxt = nxt.getNext();
                                if (nxt!=null && !isUncond(op)) succ.add(indexMap.get(nxt));
                                if (ain instanceof JumpInsnNode) {
                                    Integer to = firstIndexOfSafe(mn.instructions, indexMap, ((JumpInsnNode) ain).label);
                                    if (to!=null) succ.add(to);
                                } else if (ain instanceof TableSwitchInsnNode) {
                                    TableSwitchInsnNode ts = (TableSwitchInsnNode) ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ts.dflt);
                                    if (d!=null) succ.add(d);
                                    for (LabelNode l : ts.labels) {
                                        Integer to = firstIndexOfSafe(mn.instructions, indexMap, l);
                                        if (to!=null) succ.add(to);
                                    }
                                } else if (ain instanceof LookupSwitchInsnNode) {
                                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode) ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ls.dflt);
                                    if (d!=null) succ.add(d);
                                    for (LabelNode l : ls.labels) {
                                        Integer to = firstIndexOfSafe(mn.instructions, indexMap, l);
                                        if (to!=null) succ.add(to);
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
        static Integer firstIndexOfSafe(InsnList insns, Map<AbstractInsnNode,Integer> map, LabelNode ln) {
            if (ln == null) return null;
            AbstractInsnNode a = ln;
            while (a != null && !map.containsKey(a)) a = a.getNext();
            return (a==null) ? null : map.get(a);
        }
        static String normalize(AbstractInsnNode ain) {
            int op = ain.getOpcode();
            if (op<0) return "unknown";
            String base = org.objectweb.asm.util.Printer.OPCODES[op].toLowerCase();
            if (ain instanceof VarInsnNode) {
                int v = ((VarInsnNode)ain).var;
                if ((base.endsWith("load")||base.endsWith("store")) && v>=0 && v<=3) return base+"_"+v;
            }
            if (ain instanceof LdcInsnNode) {
                Object c = ((LdcInsnNode)ain).cst;
                if (c instanceof Float) {
                    float f = (Float)c;
                    if (f==0f) return "fconst_0"; if (f==1f) return "fconst_1"; if (f==2f) return "fconst_2";
                }
                if (c instanceof Integer) {
                    int iv = (Integer)c;
                    switch (iv) { case -1:return "iconst_m1"; case 0:return "iconst_0"; case 1:return "iconst_1";
                        case 2:return "iconst_2"; case 3:return "iconst_3"; case 4:return "iconst_4"; case 5:return "iconst_5"; }
                }
            }
            return base;
        }
    }

    // =========================================
    // ByteTok 파서/정규화 (+ 바이트 오프셋/길이 계산)
    // =========================================
    static class ByteTokEntry {
        int index;
        String instrName;
        String opcodeHex;
        String rawLine;
        int byteIndex; // 메서드 내 바이트 오프셋
        int size;      // 바이트 길이
    }
    static class ByteTokMethod { String methodIdLine; List<ByteTokEntry> entries = new ArrayList<>(); }
    static class ByteTokFile { List<ByteTokMethod> methods = new ArrayList<>(); }

    static ByteTokFile parseByteTokByMethod(String path) throws IOException {
        Path p = Paths.get(path);
        if (!Files.exists(p)) {
            System.err.println("[WARN] ByteTok file not found: " + p.toAbsolutePath());
            return new ByteTokFile();
        }
        List<String> lines = Files.readAllLines(p);
        ByteTokFile out = new ByteTokFile();
        ByteTokMethod cur = null; int localIdx=0; int curByteIndex=0;
        for (String raw : lines) {
            String t = raw.trim();
            if (t.startsWith("Method:")) {
                cur = new ByteTokMethod(); cur.methodIdLine=t; out.methods.add(cur);
                localIdx=0; curByteIndex=0; continue;
            }
            if (cur==null) continue;
            if (t.startsWith("- ") && t.toLowerCase().contains(" instruction:")) {
                String[] parts = t.split("instruction:");
                if (parts.length < 2) continue;
                String nameRaw = parts[0].substring(2).trim();
                String hex = parts[1].trim().toUpperCase().replaceAll("\\s+","");
                String norm = normalizeTok(nameRaw, hex);

                ByteTokEntry e = new ByteTokEntry();
                e.index=localIdx++; e.instrName=norm; e.opcodeHex=hex; e.rawLine=t;
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
        String n = (nameRaw==null?"":nameRaw).toLowerCase();
        if (n.equals("aload_n")) return indexFrom(hex, "aload");
        if (n.equals("iload_n")) return indexFrom(hex, "iload");
        if (n.equals("fload_n")) return indexFrom(hex, "fload");
        if (n.equals("dload_n")) return indexFrom(hex, "dload");
        if (n.equals("lload_n")) return indexFrom(hex, "lload");
        if (n.equals("istore_n")) return indexFrom(hex, "istore");
        if (n.equals("fstore_n")) return indexFrom(hex, "fstore");
        if (n.equals("i_const") || n.equals("iconst")) {
            if (hex != null && hex.length()>=2) {
                if (hex.startsWith("02")) return "iconst_m1";
                if (hex.startsWith("03")) return "iconst_0";
                if (hex.startsWith("04")) return "iconst_1";
                if (hex.startsWith("05")) return "iconst_2";
                if (hex.startsWith("06")) return "iconst_3";
                if (hex.startsWith("07")) return "iconst_4";
                if (hex.startsWith("08")) return "iconst_5";
            }
            return "iconst";
        }
        if (n.equals("f_const") || n.equals("fconst")) {
            if (hex != null && hex.length()>=2) {
                if (hex.startsWith("0B")) return "fconst_0";
                if (hex.startsWith("0C")) return "fconst_1";
                if (hex.startsWith("0D")) return "fconst_2";
            }
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
            if (hex == null || hex.length() < 2) return base;
            int op = Integer.parseInt(hex.substring(0,2), 16);
            if ("aload".equals(base) && op>=0x2A && op<=0x2D) return "aload_" + (op-0x2A);
            if ("iload".equals(base) && op>=0x1A && op<=0x1D) return "iload_" + (op-0x1A);
            if ("fload".equals(base) && op>=0x22 && op<=0x25) return "fload_" + (op-0x22);
            if ("dload".equals(base) && op>=0x26 && op<=0x29) return "dload_" + (op-0x26);
            if ("lload".equals(base) && op>=0x1E && op<=0x21) return "lload_" + (op-0x1E);
            if ("istore".equals(base) && op>=0x3B && op<=0x3E) return "istore_" + (op-0x3B);
            if ("fstore".equals(base) && op>=0x43 && op<=0x46) return "fstore_" + (op-0x43);
        } catch (Exception ignore) {}
        return base;
    }

    // =========================================
    // 매칭/정렬/선택
    // =========================================
    static class AlignResult { int[] tokToAsm; int[] asmToTok; int score; }
    static AlignResult align(MethodBC mb, ByteTokMethod tm) {
        List<String> A = new ArrayList<>(); // ASM
        for (MethodBC.BCInsn bi : mb.insns) A.add(bi.mnemonic);

        List<String> B = new ArrayList<>(); // TOK
        for (ByteTokEntry be : tm.entries) B.add(be.instrName);

        int n=B.size(), m=A.size();
        int[][] dp = new int[n+1][m+1];
        int MATCH=2, MISMATCH=-1, GAP=-1;

        for (int i=1;i<=n;i++) dp[i][0] = dp[i-1][0] + GAP;
        for (int j=1;j<=m;j++) dp[0][j] = dp[0][j-1] + GAP;
        for (int i=1;i<=n;i++) {
            for (int j=1;j<=m;j++) {
                dp[i][j] = max3(
                        dp[i-1][j-1] + score(B.get(i-1), A.get(j-1), MATCH, MISMATCH),
                        dp[i-1][j] + GAP,
                        dp[i][j-1] + GAP
                );
            }
        }

        int i=n, j=m;
        int[] tokToAsm = new int[n]; Arrays.fill(tokToAsm,-1);
        int[] asmToTok = new int[m]; Arrays.fill(asmToTok,-1);
        while (i>0 || j>0) {
            int diag = (i>0 && j>0) ? dp[i-1][j-1] + score(B.get(i-1), A.get(j-1), MATCH, MISMATCH) : Integer.MIN_VALUE/4;
            int up   = (i>0) ? dp[i-1][j] + GAP : Integer.MIN_VALUE/4;
            int left = (j>0) ? dp[i][j-1] + GAP : Integer.MIN_VALUE/4;
            if (i>0 && j>0 && dp[i][j] == diag) {
                if (isMatch(B.get(i-1), A.get(j-1))) { tokToAsm[i-1]=j-1; asmToTok[j-1]=i-1; }
                i--; j--;
            } else if (i>0 && dp[i][j] == up) i--;
            else j--;
        }
        AlignResult ar = new AlignResult(); ar.tokToAsm=tokToAsm; ar.asmToTok=asmToTok; ar.score=dp[n][m];
        return ar;
    }
    static int score(String t, String a, int MATCH, int MISMATCH){ return isMatch(t,a) ? MATCH : MISMATCH; }
    static boolean isMatch(String t, String a){ return t.equals(a) || t.startsWith(a) || a.startsWith(t); }
    static int max3(int a,int b,int c){ return Math.max(a, Math.max(b,c)); }

    static class MethodKey {
        String owner, name, desc;
        MethodKey(String o,String n,String d){owner=o;name=n;desc=d;}
        @Override public boolean equals(Object o){
            if (this==o) return true;
            if (!(o instanceof MethodKey)) return false;
            MethodKey k=(MethodKey)o;
            return Objects.equals(owner,k.owner)&&Objects.equals(name,k.name)&&Objects.equals(desc,k.desc);
        }
        @Override public int hashCode(){ return Objects.hash(owner,name,desc); }
    }

    // ByteTok의 Method: 라인에서 (가능한 경우) owner/name/desc 추출
    static MethodKey parseMethodKey(String methodIdLine) {
        if (methodIdLine == null) return null;
        // 예시 허용: "Method: edu.pkg.Clz.method(II)I" 또는 "Method: owner.name desc=...(...)..."
        String line = methodIdLine.trim();
        if (!line.toLowerCase().startsWith("method:")) return null;
        String rest = line.substring(7).trim();

        // 가장 단순한 패턴: 마지막 점(.) 기준으로 name 분리, 이어서 JVM desc 괄호(...) 찾기
        int paren = rest.indexOf('(');
        if (paren > 0) {
            // owner.name...  name는 마지막 '.' 이후, desc는 '('부터 ')'까지 포함
            int lastDot = rest.lastIndexOf('.', paren);
            if (lastDot > 0) {
                String owner = rest.substring(0, lastDot);
                String name = rest.substring(lastDot+1, paren).replaceAll("\\s+","");
                int close = rest.indexOf(')', paren);
                if (close > paren) {
                    String desc = rest.substring(paren, close+1);
                    return new MethodKey(owner.replace('/','.'), name, desc);
                }
            }
        }
        // 폴백: owner/name없이 name만
        String simple = rest.replaceAll("\\s+","");
        return new MethodKey(null, simple, null);
    }

    static Map<MethodKey, ByteTokMethod> indexBtokByMethodKey(ByteTokFile btok) {
        Map<MethodKey, ByteTokMethod> m = new HashMap<>();
        for (ByteTokMethod tm : btok.methods) {
            MethodKey k = parseMethodKey(tm.methodIdLine);
            if (k != null) m.put(k, tm);
        }
        return m;
    }

    private static Map<String, List<MethodBC>> indexAsmByName(List<MethodBC> bcMethods) {
        Map<String, List<MethodBC>> m = new HashMap<>();
        for (MethodBC mb : bcMethods) {
            m.computeIfAbsent(mb.name, k -> new ArrayList<>()).add(mb);
        }
        return m;
    }

    private static MethodBC findAsmMethodForSoot(SootMethod sm, Map<String, List<MethodBC>> asmIndex) {
        List<MethodBC> candidates = asmIndex.get(sm.getName());
        if (candidates == null || candidates.isEmpty()) return null;
        if (candidates.size() == 1) return candidates.get(0);
        int sootParams = sm.getParameterCount();
        for (MethodBC mb : candidates) {
            int asmParams = approxParamCountFromDesc(mb.desc);
            if (asmParams == sootParams) return mb;
        }
        return candidates.get(0);
    }

    private static int approxParamCountFromDesc(String desc) {
        if (desc == null || !desc.startsWith("(")) return -1;
        int c = 0;
        for (int i=1; i<desc.length(); i++) {
            char ch = desc.charAt(i);
            if (ch == ')') break;
            if (ch == '[') continue;
            if (ch == 'L') { c++; while (i<desc.length() && desc.charAt(i)!=';') i++; }
            else { c++; }
        }
        return c;
    }

    static class MatchResult {
        ByteTokMethod tm;
        AlignResult ar;
        MatchResult(ByteTokMethod tm, AlignResult ar){ this.tm=tm; this.ar=ar; }
    }

    // ASM 메서드에 최적의 ByteTok 메서드 선택
    static MatchResult selectTokForAsm(MethodBC mb, ByteTokFile btok, Map<MethodKey, ByteTokMethod> btokByKey) {
        if (btok == null || btok.methods.isEmpty()) return null;

        // 1) MethodKey가 정확히 매칭되면 그걸 사용
        MethodKey want = new MethodKey(mb.owner, mb.name, mb.desc);
        ByteTokMethod exact = btokByKey.get(want);
        if (exact != null) return new MatchResult(exact, align(mb, exact));

        // 2) 이름이 같은 후보만 추려서 최고 점수 선택
        List<ByteTokMethod> candidates = new ArrayList<>();
        for (ByteTokMethod tm : btok.methods) {
            MethodKey k = parseMethodKey(tm.methodIdLine);
            if (k != null && mb.name.equals(k.name)) candidates.add(tm);
        }
        if (candidates.isEmpty()) candidates = btok.methods;

        AlignResult bestAr = null;
        ByteTokMethod bestTm = null;
        int bestScore = Integer.MIN_VALUE/4;
        for (ByteTokMethod tm : candidates) {
            AlignResult ar = align(mb, tm);
            if (ar.score > bestScore) { bestScore = ar.score; bestAr = ar; bestTm = tm; }
        }
        return (bestTm==null) ? null : new MatchResult(bestTm, bestAr);
    }

    // =========================================
    // 유틸
    // =========================================
    private static int getLine(soot.Unit u) {
        // (현재 출력에는 사용 안 하지만, 디버깅용으로 유지 가능)
        for (soot.tagkit.Tag t : (Collection<soot.tagkit.Tag>)u.getTags()) {
            if (t instanceof SourceLineNumberTag) return ((SourceLineNumberTag)t).getLineNumber();
            if (t instanceof LineNumberTag) return ((LineNumberTag)t).getLineNumber();
        }
        return -1;
    }
}