
package com.example;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.util.Printer;

import soot.*;
import soot.options.Options;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.tagkit.SourceLineNumberTag;
import soot.tagkit.LineNumberTag;
import soot.tagkit.Tag;
import soot.jimple.*;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.*;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * GraphMappingGenerator
 *
 * 입력(고정):
 *   - classFile:  src/main/resources/edu/handong/csee/isel/machinelearning/DNN_node.class
 *   - bytetok:    src/main/resources/bytetok.txt
 *
 * 출력(옵션 없음: 둘 다 생성):
 *   - output/mapping_<owner>_<method>_<descHash>.json  (ASM↔ByteTok 매핑: tok_id, byte_index, size, hex)
 *   - output/graph_<owner>_<method>_<descHash>.json    (CFG + DFG)
 *
 * 옵션:
 *   --emitMappingOnly  : 매핑만 생성
 *   --emitGraphOnly    : 그래프만 생성(CFG+DFG)
 *   --emitCFG          : 그래프 중 CFG만 생성
 *   --emitDFG          : 그래프 중 DFG만 생성
 *   --callgraph        : Spark 포인터 분석을 켜 호출 그래프 주석 추가(기본 OFF)
 *
 * DFG:
 *   - defuse: Def(ASM) -> Use(ASM), var
 *   - flow  : Def(srcVar)(ASM) -> LHS 정의 지점(ASM), var_from, var_to
 */
public class GraphMappingGenerator {

    private static final String DEFAULT_CLASS_PATH   = "src/main/resources/edu/handong/csee/isel/machinelearning/DNN_node.class";
    private static final String DEFAULT_BYTETOK_PATH = "src/main/resources/bytetok.txt";

    public static void main(String[] args) throws Exception {
        Path classFile = Paths.get(DEFAULT_CLASS_PATH).toAbsolutePath();
        Path btokFile  = Paths.get(DEFAULT_BYTETOK_PATH).toAbsolutePath();

        boolean EMIT_MAPPING_ONLY = false;
        boolean EMIT_GRAPH_ONLY   = false;
        boolean EMIT_CFG_ONLY     = false;
        boolean EMIT_DFG_ONLY     = false;
        boolean ENABLE_CALLGRAPH  = false;

        for (int i=0; args!=null && i<args.length; i++){
            String a = (args[i]==null) ? "" : args[i].trim().toLowerCase();
            if ("--emitmappingonly".equals(a)) EMIT_MAPPING_ONLY = true;
            else if ("--emitgraphonly".equals(a)) EMIT_GRAPH_ONLY = true;
            else if ("--emitcfg".equals(a)) EMIT_CFG_ONLY = true;
            else if ("--emitdfg".equals(a)) EMIT_DFG_ONLY = true;
            else if ("--callgraph".equals(a)) ENABLE_CALLGRAPH = true;
        }
        boolean EMIT_BOTH = (!EMIT_MAPPING_ONLY && !EMIT_GRAPH_ONLY && !EMIT_CFG_ONLY && !EMIT_DFG_ONLY);

        System.out.println("[INFO] Class file:  " + classFile);
        System.out.println("[INFO] ByteTok file:" + btokFile);

        if (!Files.exists(classFile)) {
            System.err.println("[ERROR] Class file not found: " + classFile);
            return;
        }
        if (!Files.exists(btokFile)) {
            System.err.println("[ERROR] ByteTok file not found: " + btokFile);
            return;
        }

        byte[] classBytes = readAllBytesCompat(classFile.toFile());

        // ASM: .class 파싱 → 명령/CFG
        List<MethodBC> asmMethods = AsmUtil.readClassAndCFG(classBytes);

        // binaryName
        Path root = detectClasspathRoot(classFile);
        String binaryName = toBinaryNameFromPath(classFile, root);
        System.out.println("[INFO] classpathRoot=" + root);
        System.out.println("[INFO] binaryName=" + binaryName);

        // ByteTok 파싱/정규화 (BufferedReader)
        String btText = readTextCompat(btokFile.toFile(), "UTF-8");
        ByteTokFile btok = ByteTokParser.parse(btText);
        System.out.println("[INFO] ByteTok methods parsed: " + btok.methods.size());

        // Soot 초기화(항상)
        SootClass sc = null;
        try {
            sc = initSootAndLoad(binaryName, root.toString(), ENABLE_CALLGRAPH);
            System.out.println("[INFO] Soot loaded class: " + sc.getName());
        } catch (Throwable t) {
            System.err.println("[WARN] Soot load failed: " + t.getMessage());
        }

        File outDir = new File("output"); if (!outDir.exists()) outDir.mkdirs();
        Gson gson = new GsonBuilder().setPrettyPrinting().create();

        // 메서드 루프
        for (MethodBC mb : asmMethods) {
            // ByteTok 최적 선택 + DP 정렬
            MatchSelection sel = Align.alignBest(mb, btok.methods);
            if (sel == null) {
                System.err.println("[WARN] No ByteTok candidate for " + mb.owner + "." + mb.name + mb.desc);
                continue;
            }

            // 강제 매칭으로 모든 노드에 byte_index/size/hex 채우기
            List<Map<String, Object>> mapping = ForceMatch.forceFill(mb, sel.tm, sel.ar);
            int missing = 0;
            for (Map<String,Object> m : mapping) {
                Object bi = m.get("byte_index");
                if (bi == null || toInt(bi, -1) == -1) missing++;
            }

            // 매핑 JSON
            Map<String,Object> mapJson = new LinkedHashMap<String,Object>();
            mapJson.put("method", binaryName + "." + mb.name + (mb.desc == null ? "" : mb.desc));
            mapJson.put("map", mapping);
            mapJson.put("method_code_size", sel.tm.methodCodeSize);
            mapJson.put("align_score", sel.ar.score);
            mapJson.put("missing_count", missing);
            mapJson.put("btok_method_index", sel.tm.methodIndex);

            String ownerSafe = (binaryName == null ? "unknown" : binaryName).replace('.', '_');
            String methSafe  = sanitize(mb.name);
            String descHash  = Integer.toHexString((mb.desc == null ? "" : mb.desc).hashCode());
            File mapOut      = new File(outDir, "mapping_" + ownerSafe + "_" + methSafe + "_" + descHash + ".json");

            if (EMIT_BOTH || EMIT_MAPPING_ONLY) {
                writeJsonCompat(mapOut, gson.toJson(mapJson), "UTF-8");
                System.out.println("✅ Saved mapping " + mapOut.getAbsolutePath() + " (missing=" + missing + ")");
                if (EMIT_MAPPING_ONLY) continue; // 그래프 필요 없으면 다음 메서드
            }

            // 그래프(JSON): CFG + DFG
            Map<String,Object> graphJson = buildGraphAndDFGJson(mb, sel, sc, ENABLE_CALLGRAPH, EMIT_CFG_ONLY, EMIT_DFG_ONLY);

            if (EMIT_BOTH || EMIT_GRAPH_ONLY || EMIT_CFG_ONLY || EMIT_DFG_ONLY) {
                File graphOut = new File(outDir, "graph_" + ownerSafe + "_" + methSafe + "_" + descHash + ".json");
                writeJsonCompat(graphOut, gson.toJson(graphJson), "UTF-8");
                System.out.println("📄 Saved graph " + graphOut.getAbsolutePath());
            }
        }

        System.out.println("[INFO] Done.");
    }

    // ===================== ASM 수집 + CFG =====================
    static class MethodBC {
        String owner, name, desc;
        static class BCInsn {
            int index;
            int line;             // 라인 정보(ASM LineNumberNode)
            String mnemonic;
            // ByteTok 병합 대상
            int byteIndex = -1;
            int size = -1;
            String hex = null;
        }
        List<BCInsn> insns = new ArrayList<BCInsn>();
        Map<Integer, List<Integer>> edges = new HashMap<Integer, List<Integer>>(); // ASM CFG(normal)
    }

    static class AsmUtil {

        static List<MethodBC> readClassAndCFG(byte[] bytes) throws IOException {
            final List<MethodBC> out = new ArrayList<MethodBC>();
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
                    final MethodBC mb  = new MethodBC();
                    mb.owner = owner; mb.name = name; mb.desc = desc;
                    out.add(mb);
                    return new MethodVisitor(Opcodes.ASM9, mn) {
                        @Override
                        public void visitEnd() {
                            Map<AbstractInsnNode,Integer> indexMap = new IdentityHashMap<AbstractInsnNode,Integer>();
                            int idx=0, currentLine=-1;

                            // 노드 수집 (라벨/프레임 제외)
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (ain instanceof LineNumberNode) { currentLine = ((LineNumberNode)ain).line; continue; }
                                int type = ain.getType();
                                if (type == AbstractInsnNode.LABEL || type == AbstractInsnNode.FRAME) continue;

                                MethodBC.BCInsn bi = new MethodBC.BCInsn();
                                bi.index = idx;
                                bi.line  = currentLine;
                                bi.mnemonic = normalize(ain);
                                mb.insns.add(bi);
                                indexMap.put(ain, idx);
                                idx++;
                            }

                            // CFG 수집
                            for (AbstractInsnNode ain = mn.instructions.getFirst(); ain != null; ain = ain.getNext()) {
                                if (!indexMap.containsKey(ain)) continue;
                                int from = indexMap.get(ain);
                                List<Integer> succ = mb.edges.containsKey(from) ? mb.edges.get(from) : new ArrayList<Integer>();
                                mb.edges.put(from, succ);

                                int op = ain.getOpcode();
                                // implicit fall-through
                                AbstractInsnNode nxt = ain.getNext();
                                while (nxt!=null && !indexMap.containsKey(nxt)) nxt = nxt.getNext();
                                if (nxt!=null && !isUncond(op)) succ.add(indexMap.get(nxt));

                                // explicit jumps/switches
                                if (ain instanceof JumpInsnNode) {
                                    Integer to = firstIndexOfSafe(mn.instructions, indexMap, ((JumpInsnNode)ain).label);
                                    if (to!=null) succ.add(to);
                                } else if (ain instanceof TableSwitchInsnNode) {
                                    TableSwitchInsnNode ts = (TableSwitchInsnNode)ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ts.dflt); if (d!=null) succ.add(d);
                                    for (int i=0;i<ts.labels.size();i++){
                                        LabelNode l = (LabelNode) ts.labels.get(i);
                                        Integer to = firstIndexOfSafe(mn.instructions, indexMap, l);
                                        if (to!=null) succ.add(to);
                                    }
                                } else if (ain instanceof LookupSwitchInsnNode) {
                                    LookupSwitchInsnNode ls = (LookupSwitchInsnNode)ain;
                                    Integer d = firstIndexOfSafe(mn.instructions, indexMap, ls.dflt); if (d!=null) succ.add(d);
                                    for (int i=0;i<ls.labels.size();i++){
                                        LabelNode l = (LabelNode) ls.labels.get(i);
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

        static boolean isUncond(int opcode){
            return opcode == Opcodes.GOTO ||
                    opcode == Opcodes.RETURN || opcode == Opcodes.IRETURN || opcode == Opcodes.FRETURN ||
                    opcode == Opcodes.ARETURN || opcode == Opcodes.LRETURN || opcode == Opcodes.DRETURN ||
                    opcode == Opcodes.ATHROW;
        }
        static Integer firstIndexOfSafe(InsnList insns, Map<AbstractInsnNode,Integer> map, LabelNode ln){
            if (ln == null) return null;
            AbstractInsnNode a = ln;
            while (a != null && !map.containsKey(a)) a = a.getNext();
            return (a==null) ? null : map.get(a);
        }
        static String normalize(AbstractInsnNode ain){
            int op = ain.getOpcode();
            if (op<0) return "unknown";
            String base = Printer.OPCODES[op].toLowerCase();

            if (ain instanceof LdcInsnNode) {
                Object c = ((LdcInsnNode) ain).cst;
                if (c instanceof Double || c instanceof Long) return "ldc2_w";
                if (c instanceof Float) {
                    float f = ((Float)c).floatValue();
                    if (f == 0f) return "fconst_0";
                    if (f == 1f) return "fconst_1";
                    if (f == 2f) return "fconst_2";
                }
                if (c instanceof Integer) {
                    int iv = ((Integer)c).intValue();
                    if (iv == -1) return "iconst_m1";
                    if (iv == 0)  return "iconst_0";
                    if (iv == 1)  return "iconst_1";
                    if (iv == 2)  return "iconst_2";
                    if (iv == 3)  return "iconst_3";
                    if (iv == 4)  return "iconst_4";
                    if (iv == 5)  return "iconst_5";
                }
            }
            if (ain instanceof VarInsnNode) {
                int v = ((VarInsnNode)ain).var;
                if ((base.endsWith("load") || base.endsWith("store")) && v>=0 && v<=3) return base + "_" + v;
            }
            return base;
        }
    }

    // ===================== Soot 초기화/로드 =====================
    private static SootClass initSootAndLoad(String binaryName, String classDir, boolean enableCG){
        Options.v().set_prepend_classpath(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(enableCG); // callgraph 필요시만
        Options.v().set_keep_line_number(true);
        Options.v().set_no_bodies_for_excluded(true);
        List<String> ex = new ArrayList<String>();
        ex.add("java."); ex.add("javax."); ex.add("sun."); ex.add("com.sun."); ex.add("jdk.");
        ex.add("org.w3c."); ex.add("org.xml.");
        Options.v().set_exclude(ex);

        String cp = Scene.v().defaultClassPath() + File.pathSeparator + classDir;
        Options.v().set_soot_classpath(cp);
        Options.v().set_process_dir(Collections.singletonList(classDir));

        if (enableCG) {
            Options.v().setPhaseOption("cg.spark","enabled:true");
        }

        SootClass sc = Scene.v().forceResolve(binaryName, SootClass.BODIES);
        sc.setApplicationClass();
        Scene.v().loadNecessaryClasses();

        if (enableCG) {
            PackManager.v().runPacks(); // callgraph 생성
        }
        return sc;
    }

    // ===================== ByteTok 파서/정규화 =====================
    static class ByteTokEntry {
        int idx;
        String name;
        String hex;
        int byteIndex;
        int size;
        ByteTokEntry(int idx, String name, String hex, int byteIndex, int size){
            this.idx = idx; this.name = name; this.hex = hex; this.byteIndex = byteIndex; this.size = size;
        }
    }
    static class ByteTokMethod {
        int methodIndex;
        List<ByteTokEntry> entries = new ArrayList<ByteTokEntry>();
        int methodCodeSize;
    }
    static class ByteTokFile {
        List<ByteTokMethod> methods = new ArrayList<ByteTokMethod>();
    }

    static class ByteTokParser {
        private static final Map<Integer,Integer> OPSIZE = new HashMap<Integer,Integer>();
        static {
            OPSIZE.put(0x57,1); // athrow
            OPSIZE.put(0xB1,1); // return
            OPSIZE.put(0xB0,1); // areturn
            OPSIZE.put(0xAC,1); // ireturn
            OPSIZE.put(0xAD,1); // lreturn
            OPSIZE.put(0xAE,1); // freturn
            OPSIZE.put(0xAF,1); // dreturn
            OPSIZE.put(0x12,2); // ldc
            OPSIZE.put(0x13,3); // ldc_w
            OPSIZE.put(0x14,3); // ldc2_w
            OPSIZE.put(0xB4,3); // getfield
            OPSIZE.put(0xB5,3); // putfield
            OPSIZE.put(0xB6,3); // invokevirtual
            OPSIZE.put(0xB7,3); // invokespecial
            OPSIZE.put(0xB8,3); // invokestatic
            OPSIZE.put(0xA7,3); // goto
            OPSIZE.put(0x84,3); // iinc
            OPSIZE.put(0xBC,2); // newarray
            OPSIZE.put(0xC5,4); // multianewarray
        }

        static ByteTokFile parse(String content) {
            ByteTokFile out = new ByteTokFile();
            Pattern p = Pattern.compile("^\\s*Method:.*?\\n(.*?)\\n\\s*\\-\\s*LineNumberTable:", Pattern.MULTILINE | Pattern.DOTALL);
            Matcher m = p.matcher(content);
            int mi = 0;
            while (m.find()) {
                String block = m.group(1);
                ByteTokMethod tm = parseBlock(block, mi);
                tm.methodIndex = mi;
                out.methods.add(tm);
                mi++;
            }
            return out;
        }

        private static ByteTokMethod parseBlock(String block, int methodIndex) {
            ByteTokMethod tm = new ByteTokMethod();
            tm.methodIndex = methodIndex;

            int cur = 0;
            int local = 0;
            String[] lines = block.split("\\R");
            for (int i=0;i<lines.length;i++) {
                Norm n = normalizeLine(lines[i]);
                if (n == null) continue;

                int size = sizeByOpcodeHex(n.hex);
                tm.entries.add(new ByteTokEntry(local, n.name, n.hex, cur, size));
                cur += size; local++;
            }
            if (tm.entries.isEmpty()) tm.methodCodeSize = 0;
            else {
                ByteTokEntry last = tm.entries.get(tm.entries.size()-1);
                tm.methodCodeSize = last.byteIndex + last.size;
            }
            return tm;
        }

        static class Norm { String name; String hex; Norm(String name,String hex){this.name=name;this.hex=hex;} }

        private static Norm normalizeLine(String line) {
            Matcher mm = Pattern.compile("-\\s+([A-Za-z0-9_<>]+)\\s+instruction:\\s+([0-9A-F]+)", Pattern.CASE_INSENSITIVE).matcher(line);
            if (!mm.find()) return null;
            String raw = mm.group(1).toLowerCase();
            String hex = mm.group(2).toUpperCase();

            // if<cond>/if_icmp 구체화
            if ("if<cond>".equals(raw) || "if_<cond>".equals(raw)) {
                String op = hex.substring(0,2);
                String name;
                if ("99".equals(op)) name = "ifeq";
                else if ("9A".equals(op)) name = "ifne";
                else if ("9B".equals(op)) name = "iflt";
                else if ("9C".equals(op)) name = "ifge";
                else if ("9D".equals(op)) name = "ifgt";
                else if ("9E".equals(op)) name = "ifle";
                else name = "if";
                return new Norm(name, hex);
            }
            if ("if_icmp".equals(raw)) {
                String op = hex.substring(0,2);
                String name;
                if ("9F".equals(op)) name = "if_icmpeq";
                else if ("A0".equals(op)) name = "if_icmpne";
                else if ("A1".equals(op)) name = "if_icmplt";
                else if ("A2".equals(op)) name = "if_icmpge";
                else if ("A3".equals(op)) name = "if_icmpgt";
                else if ("A4".equals(op)) name = "if_icmple";
                else name = "if_icmp";
                return new Norm(name, hex);
            }

            // load/store 패밀리 인덱스 분화
            if ("aload_n".equals(raw) || "iload_n".equals(raw) || "fload_n".equals(raw) ||
                    "dload_n".equals(raw) || "lload_n".equals(raw) ||
                    "istore_n".equals(raw) || "fstore_n".equals(raw) || "astore_n".equals(raw)) {
                String base;
                if ("aload_n".equals(raw)) base="aload";
                else if ("iload_n".equals(raw)) base="iload";
                else if ("fload_n".equals(raw)) base="fload";
                else if ("dload_n".equals(raw)) base="dload";
                else if ("lload_n".equals(raw)) base="lload";
                else if ("istore_n".equals(raw)) base="istore";
                else if ("fstore_n".equals(raw)) base="fstore";
                else base="astore";
                int op = Integer.parseInt(hex.substring(0,2),16);
                Integer idx = null;
                if ("aload".equals(base) && op>=0x2A && op<=0x2D) idx = Integer.valueOf(op-0x2A);
                else if ("iload".equals(base) && op>=0x1A && op<=0x1D) idx = Integer.valueOf(op-0x1A);
                else if ("fload".equals(base) && op>=0x22 && op<=0x25) idx = Integer.valueOf(op-0x22);
                else if ("dload".equals(base) && op>=0x26 && op<=0x29) idx = Integer.valueOf(op-0x26);
                else if ("lload".equals(base) && op>=0x1E && op<=0x21) idx = Integer.valueOf(op-0x1E);
                else if ("istore".equals(base) && op>=0x3B && op<=0x3E) idx = Integer.valueOf(op-0x3B);
                else if ("fstore".equals(base) && op>=0x43 && op<=0x46) idx = Integer.valueOf(op-0x43);
                String name = (idx != null) ? (base+"_"+idx.intValue()) : base;
                return new Norm(name, hex);
            }

            // const
            if ("i_const".equals(raw) || "iconst".equals(raw)) {
                String op = hex.substring(0,2);
                String name;
                if ("02".equals(op)) name="iconst_m1";
                else if ("03".equals(op)) name="iconst_0";
                else if ("04".equals(op)) name="iconst_1";
                else if ("05".equals(op)) name="iconst_2";
                else if ("06".equals(op)) name="iconst_3";
                else if ("07".equals(op)) name="iconst_4";
                else if ("08".equals(op)) name="iconst_5";
                else name="iconst";
                return new Norm(name, hex);
            }
            if ("f_const".equals(raw) || "fconst".equals(raw)) {
                String op = hex.substring(0,2);
                String name;
                if ("0B".equals(op)) name="fconst_0";
                else if ("0C".equals(op)) name="fconst_1";
                else if ("0D".equals(op)) name="fconst_2";
                else name="fconst";
                return new Norm(name, hex);
            }

            // returns
            if ("f_return".equals(raw)) return new Norm("freturn", hex);
            if ("d_return".equals(raw)) return new Norm("dreturn", hex);
            if ("i_return".equals(raw)) return new Norm("ireturn", hex);
            if ("a_return".equals(raw)) return new Norm("areturn", hex);
            if ("l_return".equals(raw)) return new Norm("lreturn", hex);

            if ("ldc2_w".equals(raw)) return new Norm("ldc2_w", hex);

            return new Norm(raw, hex);
        }

        private static int sizeByOpcodeHex(String hex){
            if (hex == null || hex.length() < 2) return 1;
            int op;
            try { op = Integer.parseInt(hex.substring(0,2),16); } catch (Exception e){ return 1; }
            Integer s = OPSIZE.get(op);
            if (s != null) return s;
            String cleaned = hex.replaceAll("[^0-9A-F]","");
            int len = cleaned.length()/2;
            if (len <= 0) len = 1;
            return len;
        }
    }

    // ===================== 정렬/선택 =====================
    static class AlignResult { int[] tokToAsm; int[] asmToTok; int score; }
    static class MatchSelection { ByteTokMethod tm; AlignResult ar; MatchSelection(ByteTokMethod tm, AlignResult ar){ this.tm=tm; this.ar=ar; } }

    static class Align {
        static MatchSelection alignBest(MethodBC mb, List<ByteTokMethod> tokMethods){
            if (tokMethods == null || tokMethods.isEmpty()) return null;

            List<String> A = new ArrayList<String>();
            for (int i=0;i<mb.insns.size();i++) A.add(mb.insns.get(i).mnemonic);

            int bestScore = Integer.MIN_VALUE/4;
            ByteTokMethod bestTm = null;
            AlignResult bestAr = null;

            for (int k=0;k<tokMethods.size();k++) {
                ByteTokMethod tm = tokMethods.get(k);
                List<String> B = new ArrayList<String>();
                for (int i=0;i<tm.entries.size();i++) B.add(tm.entries.get(i).name);

                AlignResult ar = dpAlign(A, B);
                if (ar.score > bestScore) {
                    bestScore = ar.score; bestTm = tm; bestAr = ar;
                }
            }
            if (bestTm == null) return null;
            return new MatchSelection(bestTm, bestAr);
        }

        private static AlignResult dpAlign(List<String> A, List<String> B){
            int m = A.size(), n = B.size();
            int[][] dp = new int[n+1][m+1];
            int GAP = -1;

            for (int i=1;i<=n;i++) dp[i][0] = dp[i-1][0] + GAP;
            for (int j=1;j<=m;j++) dp[0][j] = dp[0][j-1] + GAP;

            for (int i=1;i<=n;i++){
                for (int j=1;j<=m;j++){
                    int s = score(B.get(i-1), A.get(j-1));
                    int d = dp[i-1][j-1] + s;
                    int u = dp[i-1][j] + GAP;
                    int l = dp[i][j-1] + GAP;
                    int max = d;
                    if (u > max) max = u;
                    if (l > max) max = l;
                    dp[i][j] = max;
                }
            }

            int i=n, j=m;
            int[] tokToAsm = new int[n]; Arrays.fill(tokToAsm, -1);
            int[] asmToTok = new int[m]; Arrays.fill(asmToTok, -1);

            while (i>0 || j>0) {
                int s = (i>0 && j>0) ? score(B.get(i-1), A.get(j-1)) : -999999;
                int d = (i>0 && j>0) ? (dp[i-1][j-1] + s) : -999999;
                int u = (i>0) ? (dp[i-1][j] + GAP) : -999999;
                int l = (j>0) ? (dp[i][j-1] + GAP) : -999999;
                if (i>0 && j>0 && dp[i][j] == d) {
                    if (s >= 1) { tokToAsm[i-1] = j-1; asmToTok[j-1] = i-1; }
                    i--; j--;
                } else if (i>0 && dp[i][j] == u) {
                    i--;
                } else {
                    j--;
                }
            }
            AlignResult ar = new AlignResult();
            ar.tokToAsm = tokToAsm; ar.asmToTok = asmToTok; ar.score = dp[n][m];
            return ar;
        }

        private static int score(String t, String a){
            if (t.equals(a)) return 2;
            if (t.startsWith(a) || a.startsWith(t)) return 1;
            if (isSynonym(t,a)) return 1;
            return -1;
        }
        static boolean isSynonym(String t, String a){
            if (("ldc".equals(t) && "ldc2_w".equals(a)) || ("ldc2_w".equals(t) && "ldc".equals(a))) return true;
            if ("if".equals(t) && a.startsWith("if_")) return true;
            if ("if".equals(a) && t.startsWith("if_")) return true;
            return false;
        }
    }

    // ===================== 강제 매칭(누락 제거) =====================
    static class ForceMatch {
        static List<Map<String,Object>> forceFill(MethodBC mb, ByteTokMethod tm, AlignResult ar) {
            List<MethodBC.BCInsn> nodes = mb.insns;
            int[] tokToAsm = Arrays.copyOf(ar.tokToAsm, ar.tokToAsm.length);
            int[] asmToTok = Arrays.copyOf(ar.asmToTok, ar.asmToTok.length);

            for (int ai=0; ai<nodes.size(); ai++){
                MethodBC.BCInsn n = nodes.get(ai);
                if (asmToTok[ai] != -1) {
                    ByteTokEntry e = tm.entries.get(asmToTok[ai]);
                    n.byteIndex = e.byteIndex; n.size = e.size; n.hex = e.hex;
                    continue;
                }

                // 윈도우 탐색(±6)
                int cand = -1; int bestscore = Integer.MIN_VALUE/4;
                int anchor = prevMatchedAsm(asmToTok, ai);
                int start  = (anchor != -1) ? asmToTok[anchor]+1 : 0;
                int end    = Math.min(tm.entries.size()-1, start+6);

                for (int ti=start; ti<=end; ti++){
                    if (tokToAsm[ti] != -1) continue;
                    int s = matchScore(tm.entries.get(ti).name, n.mnemonic);
                    String hex = tm.entries.get(ti).hex;
                    if (n.mnemonic.startsWith("invoke") && hex != null && hex.length() >= 2) {
                        String op2 = hex.substring(0,2);
                        String tokKind = invokeKindByOp(op2);
                        if (tokKind.length() > 0 && tokKind.equals(n.mnemonic)) s += 2;
                    }
                    if (s > bestscore) { bestscore = s; cand = ti; }
                }

                if (bestscore < 0) {
                    // 인덱스 근사
                    if (anchor != -1 && nodes.get(anchor).byteIndex != -1) {
                        MethodBC.BCInsn prev = nodes.get(anchor);
                        int guess = prev.byteIndex + Math.max(prev.size, 1);
                        cand = nearestUnusedTokByIndex(tokToAsm, tm, guess);
                    }
                    if (cand == -1) cand = findByKind(tokToAsm, tm, n.mnemonic);
                }

                if (cand != -1) {
                    asmToTok[ai] = cand; tokToAsm[cand] = ai;
                    ByteTokEntry e = tm.entries.get(cand);
                    n.byteIndex = e.byteIndex; n.size = e.size; n.hex = e.hex;
                } else {
                    // 최후 폴백: 이전 노드 기반 추정
                    if (anchor != -1 && nodes.get(anchor).byteIndex != -1) {
                        MethodBC.BCInsn prev = nodes.get(anchor);
                        n.byteIndex = prev.byteIndex + Math.max(prev.size, 1);
                        n.size = 1; n.hex = null;
                    } else {
                        n.byteIndex = 0; n.size = 1; n.hex = null;
                    }
                }
            }

            List<Map<String,Object>> mapping = new ArrayList<Map<String,Object>>();
            for (int ai=0; ai<nodes.size(); ai++){
                MethodBC.BCInsn n = nodes.get(ai);
                Map<String,Object> row = new LinkedHashMap<String,Object>();
                row.put("asm_id", ai);
                row.put("tok_id", asmToTok[ai]);
                row.put("byte_index", n.byteIndex);
                row.put("size", n.size);
                row.put("hex", n.hex);
                mapping.add(row);
            }
            return mapping;
        }

        private static int matchScore(String t, String a){
            if (t.equals(a)) return 2;
            if (t.startsWith(a) || a.startsWith(t)) return 1;
            if (Align.isSynonym(t,a)) return 1;
            return -1;
        }
        private static int prevMatchedAsm(int[] asmToTok, int ai){
            for (int k=ai-1; k>=0; k--) if (asmToTok[k] != -1) return k;
            return -1;
        }
        private static int nearestUnusedTokByIndex(int[] tokToAsm, ByteTokMethod tm, int guess){
            int best=-1, dist=Integer.MAX_VALUE;
            for (int ti=0; ti<tm.entries.size(); ti++){
                if (tokToAsm[ti] != -1) continue;
                int d = Math.abs(tm.entries.get(ti).byteIndex - guess);
                if (d < dist) { dist=d; best=ti; }
            }
            return best;
        }
        private static int findByKind(int[] tokToAsm, ByteTokMethod tm, String mnem){
            for (int ti=0; ti<tm.entries.size(); ti++){
                if (tokToAsm[ti] != -1) continue;
                String tn = tm.entries.get(ti).name;
                if (tn.equals(mnem) || Align.isSynonym(mnem, tn)) return ti;
            }
            return -1;
        }
        private static String invokeKindByOp(String op2){
            if ("B6".equals(op2)) return "invokevirtual";
            if ("B7".equals(op2)) return "invokespecial";
            if ("B8".equals(op2)) return "invokestatic";
            return "";
        }
    }

    // ===================== 그래프(JSON): CFG + DFG =====================
    private static Map<String,Object> buildGraphAndDFGJson(
            MethodBC mb, MatchSelection sel, SootClass sc, boolean enableCG, boolean emitCfgOnly, boolean emitDfgOnly) {

        Map<String,Object> out = new LinkedHashMap<String,Object>();
        List<String> warnings = new ArrayList<String>();

        // 노드(ASM)
        List<Map<String,Object>> nodesArr = new ArrayList<Map<String,Object>>();
        for (int i=0;i<mb.insns.size();i++){
            MethodBC.BCInsn bi = mb.insns.get(i);
            Map<String,Object> n = new LinkedHashMap<String,Object>();
            n.put("id", bi.index);
            n.put("mnemonic", bi.mnemonic);
            n.put("line", bi.line);
            n.put("byte_index", bi.byteIndex);
            n.put("size", bi.size);
            n.put("hex", bi.hex);
            nodesArr.add(n);
        }

        // ASM edges (normal CFG)
        List<int[]> asmEdges = new ArrayList<int[]>();
        for (Map.Entry<Integer, List<Integer>> e : mb.edges.entrySet()){
            int from = e.getKey().intValue();
            List<Integer> succ = e.getValue();
            for (int k=0;k<succ.size();k++){
                asmEdges.add(new int[]{from, succ.get(k).intValue()});
            }
        }

        // typed CFG edges
        List<Map<String,Object>> typedEdges = new ArrayList<Map<String,Object>>();

        // 구조 검사(ASM)
        for (int i=0;i<mb.insns.size();i++){
            MethodBC.BCInsn bi = mb.insns.get(i);
            String base = baseMnemonic(bi.mnemonic);
            int deg = mb.edges.containsKey(i) ? mb.edges.get(i).size() : 0;
            if ("goto".equals(base) && deg != 1) warnings.add("goto id="+i+" succ="+deg);
            if (isConditional(base) && deg != 2) warnings.add("cond("+base+") id="+i+" succ="+deg);
            if (isReturn(base) && deg != 0) warnings.add("return id="+i+" succ="+deg);
        }

        // DFG(Def-Use + Flow)
        List<Map<String,Object>> dfgEdges = new ArrayList<Map<String,Object>>();

        if (sc != null) {
            try {
                SootMethod sm = findSootMethod(sc, mb);
                if (sm == null) {
                    warnings.add("soot_method_not_found:"+mb.name);
                } else if (!sm.isConcrete()) {
                    warnings.add("soot_method_nonconcrete:"+mb.name);
                } else {
                    Body body = sm.retrieveActiveBody();

                    // CFG 보강: ExceptionalUnitGraph
                    ExceptionalUnitGraph ug = new ExceptionalUnitGraph(body);

                    // Unit 목록/토큰화 (normalizeSootStmt 없이 toString 기반)
                    List<Unit> units = new ArrayList<Unit>();
                    for (Iterator<Unit> it=body.getUnits().iterator(); it.hasNext(); ) units.add(it.next());
                    List<String> unitTokens = new ArrayList<String>();
                    for (int ui=0; ui<units.size(); ui++) unitTokens.add(tokenOf(units.get(ui)));

                    // Soot↔ASM 정렬
                    SootAlignResult sar = SootAlign.align(mb, units, unitTokens);
                    int[] asmToSoot = sar.asmToSoot;
                    int[] sootToAsm = sar.sootToAsm;
                    Map<Unit,Integer> unitIndex = sar.unitIndex;

                    // typed edges: unexceptional + exceptional
                    for (int ui=0; ui<units.size(); ui++){
                        Unit u = units.get(ui);
                        int fromAsm = sootToAsm[ui];
                        if (fromAsm < 0) continue;

                        // 정상
                        List<Unit> succsN = ug.getUnexceptionalSuccsOf(u);
                        for (int si=0; si<succsN.size(); si++){
                            Unit v = succsN.get(si);
                            Integer toAsm = sootToAsm[unitIndex.get(v)];
                            if (toAsm != null && toAsm >= 0){
                                addTypedEdge(typedEdges, fromAsm, toAsm, "normal");
                                if (!existsEdge(asmEdges, fromAsm, toAsm)) addTypedEdge(typedEdges, fromAsm, toAsm, "soot_extra");
                            }
                        }
                        // 예외
                        List<Unit> succsE = ug.getExceptionalSuccsOf(u);
                        for (int si=0; si<succsE.size(); si++){
                            Unit v = succsE.get(si);
                            Integer toAsm = sootToAsm[unitIndex.get(v)];
                            if (toAsm != null && toAsm >= 0){
                                addTypedEdge(typedEdges, fromAsm, toAsm, "exceptional");
                            }
                        }
                    }
                    warnings.add("soot_units="+units.size()+" typed_edges="+typedEdges.size());

                    // DFG 계산: SmartLocalDefs + SimpleLiveLocals
                    soot.toolkits.scalar.SimpleLiveLocals sll = new soot.toolkits.scalar.SimpleLiveLocals(ug);
                    soot.toolkits.scalar.SmartLocalDefs sld  = new soot.toolkits.scalar.SmartLocalDefs(ug, sll);

                    for (int ui=0; ui<units.size(); ui++){
                        Unit u = units.get(ui);
                        int useAsm = sootToAsm[ui];
                        if (useAsm < 0) continue;

                        // Def‑Use
                        for (ValueBox vb : u.getUseBoxes()){
                            Value v = vb.getValue();
                            if (v instanceof Local){
                                List<Unit> defs = sld.getDefsOfAt((Local)v, u);
                                for (int di=0; di<defs.size(); di++){
                                    Unit du = defs.get(di);
                                    Integer defAsm = sootToAsm[unitIndex.get(du)];
                                    if (defAsm != null && defAsm >= 0){
                                        Map<String,Object> e = new LinkedHashMap<String,Object>();
                                        e.put("from", defAsm);
                                        e.put("to", useAsm);
                                        e.put("var", ((Local)v).getName());
                                        e.put("type","defuse");
                                        dfgEdges.add(e);
                                    }
                                }
                            }
                        }

                        // Flow: x := y, x := y + z, ...
                        if (u instanceof AssignStmt){
                            AssignStmt as = (AssignStmt)u;
                            Value lhs = as.getLeftOp();
                            if (lhs instanceof Local){
                                String dst = ((Local)lhs).getName();
                                for (ValueBox vb : u.getUseBoxes()){
                                    Value v = vb.getValue();
                                    if (v instanceof Local){
                                        String src = ((Local)v).getName();
                                        List<Unit> defs = sld.getDefsOfAt((Local)v, u);
                                        for (int di=0; di<defs.size(); di++){
                                            Unit du = defs.get(di);
                                            Integer defAsm = sootToAsm[unitIndex.get(du)];
                                            if (defAsm != null && defAsm >= 0){
                                                Map<String,Object> e = new LinkedHashMap<String,Object>();
                                                e.put("from", defAsm);
                                                e.put("to", useAsm); // LHS 정의 발생 위치(현재 Unit)
                                                e.put("var_from", src);
                                                e.put("var_to", dst);
                                                e.put("type","flow");
                                                dfgEdges.add(e);
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // (선택) Callgraph 주석: 필요 시 ENABLE_CALLGRAPH 처리 가능
                        if (enableCG && ((u instanceof Stmt) && ((Stmt)u).containsInvokeExpr())) {
                            // CallGraph cg = Scene.v().getCallGraph();
                            // cg 질의하여 invoke_targets 주석 추가 가능
                        }
                    }
                }
            } catch (Throwable t) {
                warnings.add("dfg_failed:"+t.getMessage());
            }
        } else {
            warnings.add("soot_not_loaded");
        }

        // === 최종 출력 조립 ===
        Map<String,Object> g = new LinkedHashMap<String,Object>();
        g.put("nodes", nodesArr);
        g.put("edges", asmEdges);

        if (!emitDfgOnly) {
            out.put("graph", g);
            out.put("edges_typed", typedEdges);
        }

        Map<String,Object> dfg = new LinkedHashMap<String,Object>();
        dfg.put("edges", dfgEdges);                 // 비어 있어도 edges: [] 로 기록
        dfg.put("edge_count", dfgEdges.size());     // 0도 그대로
        List<String> dfgStatus = new ArrayList<String>();
        if (dfgEdges.isEmpty()) dfgStatus.add("empty");
        for (String w : warnings){
            if (w.startsWith("soot_") || w.startsWith("dfg_")) dfgStatus.add(w);
        }
        if (!dfgStatus.isEmpty()) dfg.put("status", dfgStatus);
        out.put("dfg", dfg);                        // ✅ 항상 포함

        out.put("node_count", nodesArr.size());
        if (!warnings.isEmpty()) out.put("struct_warnings", warnings);
        out.put("method_code_size", sel.tm.methodCodeSize);
        out.put("align_score", sel.ar.score);
        return out;
    }

    // ----- 문자열 기반 Soot Unit 토큰화 (normalizeSootStmt 없이) -----
    static String tokenOf(Unit u){
        String s = u.toString();
        if (s == null) return "stmt";
        s = s.toLowerCase(Locale.ROOT).trim();

        // 제어/분기
        if (s.startsWith("if ")) return "if";
        if (s.startsWith("goto")) return "goto";
        if (s.startsWith("return")) return "return";
        if (s.startsWith("throw")) return "athrow";
        if (s.startsWith("tableswitch")) return "tableswitch";
        if (s.startsWith("lookupswitch")) return "lookupswitch";

        // 호출 형태(virtual/special/static)
        if (s.contains("virtualinvoke")) return "invokevirtual";
        if (s.contains("specialinvoke")) return "invokespecial";
        if (s.contains("staticinvoke"))  return "invokestatic";

        // 기본
        return "stmt";
    }

    // ----- Soot↔ASM 정렬(라인 태그 없이, Unit 순서 기반) -----
    static class SootAlignResult {
        int[] asmToSoot;             // asm index -> unit index
        int[] sootToAsm;             // unit index -> asm index
        Map<Unit,Integer> unitIndex; // Unit -> unit index
    }
    static class SootAlign {
        static SootAlignResult align(MethodBC mb, List<Unit> units, List<String> unitTokens){
            List<String> A = new ArrayList<String>();
            for (int i=0;i<mb.insns.size();i++) A.add(mb.insns.get(i).mnemonic);

            int m=A.size(), n=unitTokens.size(), GAP=-1;
            int[][] dp = new int[n+1][m+1];
            for (int i=1;i<=n;i++) dp[i][0]=dp[i-1][0]+GAP;
            for (int j=1;j<=m;j++) dp[0][j]=dp[0][j-1]+GAP;
            for (int i=1;i<=n;i++){
                for (int j=1;j<=m;j++){
                    dp[i][j]=Math.max(dp[i-1][j-1]+score(unitTokens.get(i-1),A.get(j-1)),
                            Math.max(dp[i-1][j]+GAP, dp[i][j-1]+GAP));
                }
            }
            int[] asmToSoot = new int[m]; Arrays.fill(asmToSoot,-1);
            int[] sootToAsm = new int[n]; Arrays.fill(sootToAsm,-1);

            int i=n, j=m;
            while (i>0 || j>0){
                int s = (i>0&&j>0)? score(unitTokens.get(i-1),A.get(j-1)) : -999999;
                int diag = (i>0&&j>0)? dp[i-1][j-1]+s : -999999;
                int up   = (i>0)? dp[i-1][j]+GAP : -999999;
                int left = (j>0)? dp[i][j-1]+GAP : -999999;
                if (i>0 && j>0 && dp[i][j]==diag){
                    if (s>=1){ asmToSoot[j-1]=i-1; sootToAsm[i-1]=j-1; }
                    i--; j--;
                } else if (i>0 && dp[i][j]==up) i--;
                else j--;
            }
            Map<Unit,Integer> unitIndex = new IdentityHashMap<Unit,Integer>();
            for (int ui=0; ui<units.size(); ui++) unitIndex.put(units.get(ui), ui);

            SootAlignResult res = new SootAlignResult();
            res.asmToSoot=asmToSoot; res.sootToAsm=sootToAsm; res.unitIndex=unitIndex;
            return res;
        }
        private static int score(String t, String a){
            if (t.equals(a)) return 2;
            if (t.startsWith(a) || a.startsWith(t)) return 1;
            if ("invoke".equals(t) && a.startsWith("invoke")) return 1;
            if (t.startsWith("invoke") && "invoke".equals(a)) return 1;
            return -1;
        }
    }

    private static void addTypedEdge(List<Map<String,Object>> arr, int from, int to, String type){
        Map<String,Object> e = new LinkedHashMap<String,Object>();
        e.put("from", from); e.put("to", to); e.put("type", type);
        arr.add(e);
    }

    private static boolean existsEdge(List<int[]> edges, int from, int to){
        for (int i=0;i<edges.size();i++){
            int[] e = edges.get(i);
            if (e[0]==from && e[1]==to) return true;
        }
        return false;
    }

    private static int nullInt(){ return Integer.MIN_VALUE/4; }

    private static SootMethod findSootMethod(SootClass sc, MethodBC mb){
        if (sc == null) return null;
        List<SootMethod> methods = sc.getMethods();
        for (int i=0;i<methods.size();i++){
            SootMethod sm = methods.get(i);
            if (!sm.isConcrete()) continue;
            if (sm.getName().equals(mb.name)) {
                int sootParams = sm.getParameterCount();
                int asmParams  = approxParamCountFromDesc(mb.desc);
                if (asmParams == sootParams || asmParams < 0) return sm;
            }
        }
        return null;
    }

    private static int approxParamCountFromDesc(String desc){
        if (desc == null || !desc.startsWith("(")) return -1;
        int c = 0;
        for (int i=1; i<desc.length(); i++){
            char ch = desc.charAt(i);
            if (ch == ')') break;
            if (ch == '[') continue;
            if (ch == 'L'){ c++; while (i<desc.length() && desc.charAt(i)!=';') i++; }
            else { c++; }
        }
        return c;
    }

    private static int getLine(Unit u){
        List<Tag> tags = u.getTags();
        for (int i=0;i<tags.size();i++){
            Tag t = tags.get(i);
            if (t instanceof SourceLineNumberTag) return ((SourceLineNumberTag)t).getLineNumber();
            if (t instanceof LineNumberTag)       return ((LineNumberTag)t).getLineNumber();
        }
        return -1;
    }

    private static String baseMnemonic(String m){
        if (m==null) return "";
        if (m.startsWith("iconst")) return "iconst";
        if (m.startsWith("fconst")) return "fconst";
        if (m.startsWith("dconst")) return "dconst";
        if (m.startsWith("aload"))  return "aload";
        if (m.startsWith("iload"))  return "iload";
        if (m.startsWith("fload"))  return "fload";
        if (m.startsWith("istore")) return "istore";
        if (m.startsWith("fstore")) return "fstore";
        if (m.startsWith("astore")) return "astore";
        return m;
    }
    private static boolean isConditional(String b){ return b.startsWith("if"); }
    private static boolean isReturn(String b){ return b.endsWith("return") || "return".equals(b); }

    // ===================== 유틸/IO =====================
    static String sanitize(String s){ return (s==null) ? "null" : s.replaceAll("[^a-zA-Z0-9_]", "_"); }
    static int toInt(Object o, int def){ try{ return (o==null)?def:Integer.parseInt(String.valueOf(o)); }catch(Exception e){ return def; } }

    private static Path detectClasspathRoot(Path classFile){
        String s = classFile.toString().replace('\\','/');
        String[] roots = { "/target/classes/", "/build/classes/java/main/", "/out/production/", "/bin/", "/src/main/resources/", "/src/test/resources/", "/src/main/java/", "/src/test/java/" };
        for (int i=0;i<roots.length;i++) {
            String root = roots[i];
            int idx = s.indexOf(root);
            if (idx >= 0) {
                String rootStr = s.substring(0, idx + root.length() - 1);
                return Paths.get(rootStr);
            }
        }
        String[] pkgStarts = {"/edu/","/com/","/org/","/net/"};
        int best = Integer.MAX_VALUE; String hit = null;
        for (int i=0;i<pkgStarts.length;i++) {
            String ps = pkgStarts[i];
            int idx = s.indexOf(ps);
            if (idx >= 0 && idx < best) { best = idx; hit = ps; }
        }
        if (hit != null && best < s.length()) return Paths.get(s.substring(0, best));
        return classFile.getParent() != null ? classFile.getParent() : classFile;
    }
    private static String toBinaryNameFromPath(Path classFile, Path classpathRoot){
        String abs = classFile.toAbsolutePath().toString().replace('\\','/');
        String root = classpathRoot.toAbsolutePath().toString().replace('\\','/');
        if (!root.endsWith("/")) root += "/";
        if (abs.endsWith(".class")) abs = abs.substring(0, abs.length()-6);
        if (abs.startsWith(root)) {
            String rel = abs.substring(root.length());
            return rel.replace('/', '.');
        }
        String nameOnly = classFile.getFileName().toString();
        if (nameOnly.endsWith(".class")) nameOnly = nameOnly.substring(0, nameOnly.length()-6);
        return nameOnly;
    }

    // read/write (Files.readString/write 미사용)
    private static byte[] readAllBytesCompat(File f) throws IOException {
        ByteArrayOutputStream bout = new ByteArrayOutputStream();
        InputStream in = new FileInputStream(f);
        try {
            byte[] buf = new byte[8192];
            int r;
            while ((r = in.read(buf)) != -1) bout.write(buf, 0, r);
        } finally { in.close(); }
        return bout.toByteArray();
    }
    private static String readTextCompat(File f, String charset) throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(f), Charset.forName(charset)));
        try {
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = br.readLine()) != null) sb.append(line).append('\n');
            return sb.toString();
        } finally { br.close(); }
    }
    private static void writeJsonCompat(File f, String json, String charset) throws IOException {
        OutputStreamWriter w = new OutputStreamWriter(new FileOutputStream(f), Charset.forName(charset));
        try { w.write(json); } finally { w.close(); }
    }
}
