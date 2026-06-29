package bw;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import bw.BlockDPWithoutRD0.BlockTree.BTNode;
import bw.BranchDec.BDNode;
import tw.common.Chordal;
import tw.common.Graph;
import tw.common.TreeDecomposition;
import tw.common.XBitSet;
import tw.greedy.MMAF;
import tw.minseps.MinSepsGenerator;
import tw.sieve.SubblockSieve;

public class BlockDPWithoutRD0 {
//  static final boolean QUIET = Boolean.getBoolean("bw.quiet");
  static final boolean QUIET = true;
  static final boolean TRACE = true && !QUIET;
  static final boolean TRACE_DP = true && !QUIET;
  static final boolean TRACE_DERIVATION = true && !QUIET;
  static final boolean TRACE_GENERATE_CC = false && !QUIET;
  static final boolean TRACE_SUPPORT = false && !QUIET;
  static final boolean TRACE_CC = false && !QUIET;
  static final boolean VERIFYING = false;
  static final int MAX_BAG_SIZE = 100;
  static final int Block_EXCLUDE_MAX = 2;

  Graph g;
  int k;

  Block rootBlock;
  Set<XBitSet>[] connecteds;

  MscDT[] mscDT;
  Set<XBitSet> mscs;

  Set<XBitSet> tried;

  Set<Block> blocks;
  Map<XBitSet, Block> blockMap;
  BlockTree[] blockDT;

  SubblockSieve[] sieve;

  BranchDec branchDec;

  int chunk;
  int count;

  long t0;


  public BlockDPWithoutRD0(Graph g) {
    this.g = g;
    assert g.isConnected(g.all);
    assert g.minDegree() >= 2;
    assert g.n >= 3;
    chunk = (int) Math.sqrt((double) g.n) + 1; 
    if (TRACE) {
      System.out.println("BlockDP n " + g.n + " chunk " + chunk);
    }
    
    g.save("debugInst.gr");

  }

  void decompose() {    
    k = 2 * (g.minDegree() + 1) / 3;
    assert k >= 2;
    blockMap = new HashMap<>();
    rootBlock = makeBlock(g.all);
    while (k <= Math.ceil(((double) g.n) * 2.0 / 3.0)) {
      assert 3 * k / 2 <= g.n;
      if(TRACE) {
        System.out.println("generating blocks for k " + k);
      }
      generateBlocks();
      if(TRACE) {
        System.out.println(blockMap.size() + " blocks for k " + k);
        summarizeBlocks();
      }

      dp();

      if (TRACE_DP) {
        Block[] ba = new Block[blockMap.size()];
        blockMap.values().toArray(ba);
        Arrays.sort(ba, (b1, b2) -> -XBitSet.cardinalityComparator.compare(b1.core, b2.core));
        for (Block block: ba) {
          if (block.derivation != null) {
            System.out.println("k " + k + " feasible " + block);
          }
        }
      }

      if (rootBlock.derivation != null) {
        Set<XBitSet> allEdges = allEdges();
        branchDec = new BranchDec(g);
        branchDec.root = rootBlock.derivation.toBD(branchDec, allEdges);
        assert allEdges.isEmpty():allEdges;
        branchDec.validate();
        if (TRACE) {
          branchDec.root.printTree(0);
          System.out.println("width " + branchDec.width());
        }
        return;
      }
      k++;
    }

  }

  void generateBlocks() {
    if (TRACE_GENERATE_CC) {
      System.out.println("generating Blocks k " + k);
    }
    blocks = new HashSet<>();
    MinSepsGenerator msg = new MinSepsGenerator(g, k);
    msg.generate();
    mscs = new HashSet<>();
    for (XBitSet sep: msg.minSeps) {
      ArrayList<XBitSet> fulls = g.fullComponents(sep);
      for (XBitSet full: fulls) {
        mscs.add(full);
        blocks.add(makeBlock(g.closedNeighborSet(full)));
      }
    }
    if (TRACE_GENERATE_CC) {
      System.out.println(mscs.size() + " minimally separated components k " + k);
    }

    mscDT = new MscDT[g.n];
    for (int v = 0; v < g.n; v++) {
      mscDT[v] = new MscDT(new HashSet<>());
    }
    for (XBitSet msc: mscs) {
      int v0 = msc.nextSetBit(0);
      mscDT[v0].add(msc);
    }

    generateBlocksCombining(g.all, new XBitSet());

    if (TRACE_GENERATE_CC) {
      System.out.println(blocks.size() + " connected Blocks generated");
    }
  }

  void generateBlocksCombining(XBitSet scope, XBitSet subsep) {
    assert !scope.intersects(subsep);
    if (scope.isEmpty()) {
      return;
    }
    if (subsep.cardinality() == k) {
      ArrayList<XBitSet> fulls = g.fullComponents(subsep);
      for (XBitSet full: fulls) {
        blocks.add(makeBlock(full.unionWith(subsep)));
      }
      return;
    }
    int v0 = scope.nextSetBit(0);
    ArrayList<XBitSet> combinables = mscDT[v0].collectCombinables(scope, subsep);
    if (VERIFYING) {
      Set<XBitSet> combinables1 = naiveCombinables(v0, scope, subsep);
      if (combinables.size() != combinables1.size()) {
        System.out.println(combinables1.size() + " true combinables while " + combinables.size() + 
            " combinalbes retrieved");
        System.out.println(" v0 " + v0 + " scope " + scope);
        for (XBitSet c: combinables1) {
          System.out.println("    " + c);
        }
        System.out.println(mscDT[v0].root.bag);
        assert false;
      }
    }
    if (TRACE_GENERATE_CC) {
      System.out.println(combinables.size() + " combinables for v0 " + v0 +
          " subsep " + subsep + " scope " + scope);
      for (XBitSet c: combinables) {
        System.out.println("   " + c + " sep " + g.neighborSet(c));
      }
    }
    for (XBitSet c: combinables) {    
      XBitSet scope1 = scope.subtract(g.closedNeighborSet(c));
      XBitSet subsep1 = subsep.unionWith(g.neighborSet(c));
      assert subsep1.cardinality() <= k;
      if (!g.neighborSet(scope1).equals(subsep1)) {
        //        System.out.println("nb of scope1 " + g.neighborSet(scope1));
        //        System.out.println("subsep1 " + subsep1 + " scope1 " + scope1);
        continue;
      }
      if (g.isConnected(scope1)) {
        Block Block = makeBlock(g.closedNeighborSet(scope1));
        blocks.add(Block);
      }
      generateBlocksCombining(scope1, subsep1);
    }
    XBitSet scope1 = scope.removeBit(v0);
    XBitSet subsep1 = subsep.addBit(v0);
    generateBlocksCombining(scope1, subsep1);
  }

  Set<XBitSet> naiveCombinables(int v0, XBitSet scope, XBitSet sep) {
    Set<XBitSet> result = new HashSet<>();
    for (XBitSet msc: mscs) {
      if (msc.nextSetBit(0) == v0 && msc.isSubset(scope) &&
          sep.unionWith(g.neighborSet(msc)).cardinality() <= k) {
        result.add(msc);
      }
    }
    return result;
  }
  
  int universalUB() {
    int ub = 2 * g.n / 3;
    if (g.n % 3 != 0) {
      ub++;
    }  
    return ub;
  }

  XBitSet boundary(XBitSet vs) {
    return g.neighborSet(g.all.subtract(vs));
  }

  boolean isSmall(XBitSet compo, XBitSet sep) {
    return compo.cardinality() * 2 + sep.cardinality() <= g.n;
  }

  void generateSubsets(int i, int n, XBitSet s, Set<XBitSet> store) {
    if (i == n) {
      store.add(s);
      return;
    }
    generateSubsets(i + 1, n, s, store);
    generateSubsets(i + 1, n, s.addBit(i), store);
  }

  Set<XBitSet> subsetsOf(XBitSet set, int m) {
    assert m <= set.cardinality();
    Set<XBitSet> store = new HashSet<>();
    generateSubsets(set.toArray(), 0, m, new XBitSet(), store);
    return store;
  }

  void generateSubsets(int[] a, int i, int m, XBitSet subset, Set<XBitSet> store) {
    if (subset.cardinality() == m) {
      store.add((XBitSet) subset.clone());
      return;
    }
    if (i == a.length) {
      return;
    }
    subset.set(a[i]);
    generateSubsets(a, i + 1, m, subset, store);
    subset.clear(a[i]);
    generateSubsets(a, i + 1, m, subset, store);
  }

  XBitSet union(XBitSet subs, ArrayList<XBitSet> compos) {
    XBitSet union = new XBitSet();
    for (int i: subs.toArray()) {
      union.or(compos.get(i));
    }
    return union;
  }

  void dp() {
    Block[] ba = new Block[blockMap.values().size()];
    blockMap.values().toArray(ba);
    Arrays.sort(ba, (b1, b2) -> 
    XBitSet.cardinalityComparator.compare(b1.core, b2.core));

    blockDT = new BlockTree[g.n];
    for (int v = 0; v < g.n; v++) {
      blockDT[v] = new BlockTree(new HashSet<>());
    }

    for (Block block: ba) {
      if (TRACE_DP) {
        System.out.println("looking for derivation k " + k + " " + " block " + block);
      }
      block.findDerivation();
      if (block.derivation != null) {
        if (TRACE_DP) {
          System.out.println("  ... derivation " + block.derivation);
        }
        if (!block.core.isEmpty()) {
          int v = block.core.nextSetBit(0);
          blockDT[v].add(block);
        }
      }
      else {
        if (TRACE_DP) {
          System.out.println("  ... no derivation");
        }
      }
    }

  }


  Set<XBitSet> edgeSet(XBitSet vs1, XBitSet vs2) {
    Set<XBitSet> edgeSet = new HashSet<>();
    for (int u: vs1.toArray()) {
      for (int v: g.neighborSet[u].intersectWith(vs2).toArray()) {
        edgeSet.add(new XBitSet(new int[] {u, v}));
      }
    }
    return edgeSet;
  }

  XBitSet verticesOf(Set<XBitSet> edges) {
    XBitSet vs = new XBitSet();
    for (XBitSet edge: edges) {
      vs.or(edge);
    }
    return vs;
  }

  Set<XBitSet> complements(Set<XBitSet> vss) {
    Set<XBitSet> complements = new HashSet<>();
    for (XBitSet vs: vss) {
      complements.add(g.all.subtract(vs));
    }
    return complements;
  }

  XBitSet coreOf(XBitSet f) {
    return f.subtract(bdOf(f));
  }

  XBitSet bdOf(XBitSet feasible) {
    return g.neighborSet(g.all.subtract(feasible));
  }

  XBitSet closure(XBitSet c) {
    return g.closedNeighborSet(c);
  }

  XBitSet headOf(XBitSet f, XBitSet f1, XBitSet f2) {
    XBitSet bd = bdOf(f);
    XBitSet d1 = f1.subtract(f2);
    XBitSet d2 = f2.subtract(f1);
    XBitSet m1 = d1.intersectWith(g.neighborSet(d2));
    XBitSet m2 = d2.intersectWith(g.neighborSet(d1));
    return bd.unionWith(m1).unionWith(m2);
  }

  Set<XBitSet[]> bipartitions(XBitSet s) {
    //    System.out.println("partitioning " + s);
    Set<XBitSet[]> partitions = new HashSet<>();
    for (int i = 0; i <= s.cardinality() / 2; i++) {
      Set<XBitSet> subsets = subsets(s, i);
      for (XBitSet s1: subsets) {
        XBitSet s2 = s.subtract(s1);
        if (XBitSet.cardinalityComparator.compare(s1, s2) < 0) {
          partitions.add(new XBitSet[] {s1, s2});
        }
      }
    }
    return partitions;   
  }

  Set<XBitSet> subsetsUpTo(XBitSet vs, int card) {
    if (card > vs.cardinality()) {
      card = vs.cardinality();
    }
    Set<XBitSet> sets = new HashSet<>();
    sets.add(new XBitSet());
    for (int i = 0; i < card; i++) {
      XBitSet[] sa = sets.toArray(new XBitSet[sets.size()]);
      for (XBitSet s: sa) {
        if (s.cardinality() == i) {
          for (int v: vs.subtract(s).toArray()) {
            sets.add(s.addBit(v));
          }
        }
      }
    }
    return sets;
  }

  Set<XBitSet> subsets(XBitSet vs, int card) {
    assert card <= vs.cardinality();
    Set<XBitSet> sets = new HashSet<>();
    sets.add(new XBitSet());
    for (int i = 0; i < card; i++) {
      XBitSet[] sa = sets.toArray(new XBitSet[sets.size()]);
      sets.clear();
      for (XBitSet s: sa) {
        if (s.cardinality() == i) {
          for (int v: vs.subtract(s).toArray()) {
            sets.add(s.addBit(v));
          }
        }
      }
    }
    return sets;
  }


  void summarizeBlocks() {
    System.out.println(blockMap.size() + " blocks in total");
    for (int i = 0; i <= g.n; i++) {
      if (countBlocksBySize(i) > 0) {
        System.out.println(countBlocksBySize(i) + " of cardinality " + i);
      }
    }
  }

  int countBlocksBySize(int i) {
    int count = 0;
    for (Block block: blockMap.values()) {
      if (block.core.cardinality() == i) {
        //        Block block = blockMap.get(core);
        //        System.out.println(" block " + block);
        count++;
      }
    }
    return count;
  }

  Set<XBitSet> allEdges() {
    Set<XBitSet> edges = new HashSet<>();
    for (int v = 0; v < g.n; v++) {
      for (int w: g.neighborSet[v].toArray()) {
        if (w > v) {
          edges.add(new XBitSet(new int[] {v, w}));
        }
      }
    }     
    return edges;
  }

  void verifyTree() {
    if (TRACE) {
      System.out.println("verifying the derivation tree for k " + k);
    }
    Set<XBitSet> all = allEdges();
    verifyTree(rootBlock, all, 0);
    assert all.isEmpty(): all;
  }

  void verifyTree(Block block, Set<XBitSet> remaining, int d) { 
    if (TRACE_SUPPORT) {
      System.out.println(indent(d) + block);
    }
    if (block.vs.cardinality() <= k) {
      for (int u: block.vs.toArray()) {
        for (int v: block.vs.toArray()) {
          if (u < v) {
            remaining.remove(new XBitSet(new int[] {u, v}));
          }
        }
      }
      return;
    }
    BlockDerivation derivation = block.derivation;
    assert derivation != null;
    if (TRACE_SUPPORT) {
      System.out.println(derivation);
    }
    assert derivation.block == block;
    XBitSet[] mt = derivation.midTriple;
    assert mt != null; 
    assert mt[2].cardinality() <= k: block + " " + mt[2];
    for (int u: mt[2].toArray()) {
      for (int v: mt[2].toArray()) {
        if (u < v) {
          remaining.remove(new XBitSet(new int[] {u, v}));
        }
      }
    }

    for (Block block1: derivation.subblocks) {
      verifyTree(block1, remaining, d + 1);
    }

  }

  String indent(int d) {
    StringBuilder sb = new StringBuilder();
    sb.append(d + ":");
    for (int i = 0; i < d % 80; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }

  XBitSet unionAll(XBitSet[] derivation) {
    XBitSet union = new XBitSet();
    for (XBitSet sup: derivation) {
      union.or(sup);
    }
    return union;
  }

  XBitSet boundaryOf(XBitSet vertices) {
    return g.neighborSet(g.all.subtract(vertices));
  }

  interface CombinationAcceptor{
    boolean accept(ArrayList<Block> blocks);
  }

  class BlockCombination {
    XBitSet core;
    XBitSet boundary;
    XBitSet closure;
    CombinationAcceptor acceptor;

    BlockCombination(XBitSet core, XBitSet boundary, CombinationAcceptor acceptor) {
      this.core = core;
      this.boundary = boundary;
      this.acceptor = acceptor;
      closure = core.unionWith(boundary);
    }

    void findCombination() {
      ArrayList<Block> blocks = new ArrayList<>();
      findCombination(core, boundary, blocks);
    }

    boolean findCombination(XBitSet remCore, XBitSet boundary1, ArrayList<Block> blocks) {
      if (TRACE_SUPPORT) {
        System.out.println("listCombinations remCore " + remCore + " boundary1 " + boundary1 + " blocks " + blocks.size());
      }

      if (remCore.isEmpty()) {
        XBitSet separator = closure.subtract(coreUnion(blocks));
        if (separator.cardinality() <= 3 * k / 2) {
          return acceptor.accept(blocks);
        }
        return false;
      }
      int v0 = remCore.nextSetBit(0);

      Set<Block> subblocks = new HashSet<>();
      BTNode root = blockDT[v0].root;
      root.collectSubblocks(remCore, subblocks);
      if (TRACE_SUPPORT) {
        System.out.println(subblocks.size() + " subblocks in remCore " + remCore);
      }
      for (Block sb: subblocks) {
        if (TRACE_SUPPORT) {
          System.out.println(" trying subblock " + sb);
        } 
        assert sb.core.isSubset(remCore);
        assert sb.boundary.isSubset(remCore.unionWith(boundary1));
        assert sb.core.nextSetBit(0) == v0;
        XBitSet remCore1 = remCore.subtract(sb.closure());
        XBitSet boundary2 = boundary1.unionWith(sb.boundary);
        if (boundary2.cardinality() > 3 * k / 2) {
          continue;
        }
        ArrayList<Block> blocks1 = new ArrayList<>(blocks);
        blocks1.add(sb);
        if (findCombination(remCore1, boundary2, blocks1)) {
          return true;
        }
      }
      return findCombination(remCore.removeBit(v0), boundary1.addBit(v0), blocks);
    }

  }

  class CSPair {
    XBitSet vs; 
    XBitSet sep;

    CSPair(XBitSet vs, XBitSet sep) {
      this.vs = vs;
      this.sep = sep;
    }
    @Override
    public int hashCode() {
      return vs.hashCode() + sep.hashCode();
    }
    @Override
    public boolean equals(Object x) {
      CSPair cb = (CSPair) x;
      return vs.equals(cb.vs) && sep.equals(cb.sep); 
    }
  }

  Block makeBlock(XBitSet vs) {
    assert vs != null;
    Block block = blockMap.get(vs);
    if (block == null) {
      block = new Block(vs);
      blockMap.put(vs, block);
    }
    return block;
  }

  Block singleSourceBlock(int v) {
    XBitSet BlockSet = coreOf(g.neighborSet[v].addBit(v));
    return makeBlock(BlockSet);
  }

  class Block {
    XBitSet vs;
    XBitSet boundary;
    XBitSet core;
    BlockDerivation derivation;

    Block (XBitSet vs) {
      this.vs = vs;
      boundary = g.neighborSet(g.all.subtract(vs));
      core = vs.subtract(boundary);
      assert core.isEmpty() || boundary.equals(g.neighborSet(core));
      assert g.isConnected(core);

    }

    //    void extend() {
    //      System.out.println("extending " + this);
    //      assert isSmall();
    //      for (int v: boundary.toArray()) {
    //        Block block = extendBy(v);
    //        if (block != null) {
    //          block.extend();
    //        }
    //      }
    //    }
    //
    //    Block extendBy(int v) {
    //      assert boundary.get(v);
    //      XBitSet core1 = core.addBit(v);
    //      XBitSet bd1 = boundary.unionWith(g.neighborSet[v].subtract(core));
    //      XBitSet rest = g.all.subtract(core1).subtract(bd1);
    //      XBitSet bd2 = g.neighborSet(rest);
    //      XBitSet core2 = core1.unionWith(bd1.subtract(bd2));
    //      if (blockMap.get(core2) != null) {
    //        return null;
    //      }
    //      if (core2.cardinality() * 2 + bd2.cardinality() <= g.n) {
    //        return makeBlock(core2);
    //      }
    //      else {
    //        return null;
    //      }
    //    }

    boolean isSmall() {
      return core.cardinality() * 2 + boundary.cardinality() <= g.n;
    }

    void findDerivation() {
      if (boundary.cardinality() > k) {
        return;
      }
      if (isIndependent(core) && boundary.cardinality() == 1) {
        derivation = new BlockDerivation(this, new ArrayList<Block>());
        derivation.midTriple = new XBitSet[] {boundary, new XBitSet(), new XBitSet()};
        return;
      }
      BlockCombination combi = new BlockCombination(core, boundary, new BlockAcceptor(this));
      combi.findCombination();
    }

    XBitSet closure() {
      return core.unionWith(boundary);
    }

    @Override
    public boolean equals(Object x) {
      Block Block = (Block) x;
      return core.equals(Block.core);
    }
    @Override
    public String toString() {
      return " bd " + boundary + " core " + core;
    }
  }

  class BlockAcceptor implements CombinationAcceptor {
    Block block;
    BlockAcceptor(Block block) {
      this.block = block;
    }
    public boolean accept(ArrayList<Block> blocks) {
      BlockDerivation deriv = new BlockDerivation(block, blocks);
      deriv.computeMidTriple();
      if (deriv.midTriple != null) {
        block.derivation = deriv;
        return true;
      }
      return false;
    }
  }


  XBitSet[] midTripleConforming1(XBitSet[] mt, XBitSet separator) {
    int s = separator.cardinality();
    XBitSet intersec = mt[0].intersectWith(mt[1]).intersectWith(mt[2]);
    int in = intersec.cardinality();
    if (2 * s + in > 3 * k) {
      return null;
    }
    XBitSet[] i2 = new XBitSet[3];
    for (int i = 0; i < 3; i++) {
      i2[i] = mt[i].intersectWith(mt[(i + 1) % 3]).subtract(intersec);
      if (i2[i].cardinality() + s > 2 * k) {
        return null;
      }
    }
    int[] n0 = new int[3];
    for (int i =0; i < 3; i++) {
      n0[i] = mt[i].cardinality() - intersec.cardinality();
    }
    int[] f = new int[3];
    for (int i = 0; i < 3; i++) {
      f[i] = n0[i] - 
          i2[i].cardinality() - i2[(i + 2) % 3].cardinality();
    }
    for (int f1 = 0; f1 <= f[0]; f1++) {
      for (int f2 = 0; f2 <= f[1]; f2++) {
        int s2 = n0[2] + f1 + (f[1] - f2);
        if (s2 > k) {
          continue;
        }
        int s0 = n0[0] + f2;
        if (s0 > k) {
          continue;
        }
        int s1 = n0[1] + (f[0] - f1) + f[1];
        int s01 = s0 + s1;
        if (s01 > 2 * k) {
          return null;
        }
        s0 = s01 / 2;
        s1 = s01 - s0;
        int f3 = (s01 - s0);

      }
    }
    return null;
  }

  XBitSet[] midTripleConforming(XBitSet[] mt, XBitSet separator, int k) {
    XBitSet intersec = mt[0].intersectWith(mt[1]).intersectWith(mt[2]);
    if (!intersec.isEmpty()) {
      XBitSet[] mt1 = new XBitSet[] 
          {mt[0].subtract(intersec), mt[1].subtract(intersec), mt[2].subtract(intersec)};
      XBitSet[] mt2 = midTripleConforming(mt1, separator.subtract(intersec), k - intersec.cardinality());
      if (mt2 == null) {
        return null;
      }
      XBitSet[] mt3 = new XBitSet[] 
          {mt2[0].unionWith(intersec), mt2[1].unionWith(intersec), mt2[2].unionWith(intersec)};
      return mt3;
    }
    if (nonExtendable(mt, separator, k)) {
      return null;
    }
    XBitSet[] mt1 = new XBitSet[] {(XBitSet) mt[0].clone(), (XBitSet) mt[1].clone(), (XBitSet) mt[2].clone()};
    XBitSet uncovered = separator.subtract(mt1[0]).subtract(mt1[1]).subtract(mt1[2]);
    while (!uncovered.isEmpty()) {
      int v = uncovered.nextSetBit(0);
      int i = 0;
      for (int j = 1; j < 3; j++) {
        if (mt1[j].cardinality() < mt1[i].cardinality()) {
          i = j;
        }
      }
      mt1[i].set(v);
      uncovered.clear(v);
    }
    assert !nonExtendable(mt1, separator, k);
    int s = separator.cardinality();
    int v = unsettled(mt1, separator);
    while (v >= 0) {
      assert !nonExtendable(mt1, separator, k);
      if (mt1[0].intersectWith(mt1[1]).cardinality() + s == 2 * k) {
        mt1[2] = separator.subtract(mt1[0].intersectWith(mt1[1]));
        XBitSet rem = mt1[2].subtract(mt1[0]).subtract(mt1[1]);
        int d0 = k - mt1[0].cardinality();
        assert d0 <= rem.cardinality();
        XBitSet rem0 = new XBitSet(Arrays.copyOf(rem.toArray(), d0));
        mt1[0].or(rem0);
        mt1[1].or(rem.subtract(rem0));
        assert !nonExtendable(mt1, separator, k);
        return mt1;    
      }
      if (mt1[1].intersectWith(mt1[2]).cardinality() + s == 2 * k) {
        mt1[0] = separator.subtract(mt1[1].intersectWith(mt1[2]));
        XBitSet rem = mt1[0].subtract(mt1[1]).subtract(mt1[2]);
        int d1 = k - mt1[1].cardinality();
        assert d1 <= rem.cardinality();
        XBitSet rem1 = new XBitSet(Arrays.copyOf(rem.toArray(), d1));
        mt1[1].or(rem1);
        mt1[2].or(rem.subtract(rem1));
        assert !nonExtendable(mt1, separator, k);
        return mt1;    
      }
      if (mt1[2].intersectWith(mt1[0]).cardinality() + s == 2 * k) {
        mt1[1] = separator.subtract(mt1[2].intersectWith(mt1[0]));
        XBitSet rem = mt1[2].subtract(mt1[1]).subtract(mt1[0]);
        int d2 = k - mt1[2].cardinality();
        assert d2 <= rem.cardinality();
        XBitSet rem2 = new XBitSet(Arrays.copyOf(rem.toArray(), d2));
        mt1[2].or(rem2);
        mt1[0].or(rem.subtract(rem2));
        assert !nonExtendable(mt1, separator, k);
        return mt1;    
      }
      for (int i = 0; i < 3; i++) {
        if (!mt1[i].get(v) && mt1[i].cardinality() < k) {
          mt1[i].set(v);
          break;
        }
      }
      assert doubleCovered(v, mt1);
      v = unsettled(mt1, separator);
    }
    return null;
  }

  boolean doubleCovered(int v, XBitSet[] mt) {
    int count = 0;
    for (int i = 0; i < 3; i++) {
      if (mt[i].get(v)) {
        count++;
      }
    }
    assert count <= 2;
    return count == 2;
  }

  XBitSet[] midTripleConforming2(XBitSet[] mt, XBitSet separator) {
    XBitSet[] midTriple = searchMidTriple(mt, separator);
    if (midTriple != null) {
      assert midTriple[0].cardinality() <= k;
      assert midTriple[1].cardinality() <= k;
      assert midTriple[2].cardinality() <= k;
      assert mt[0].isSubset(midTriple[0]);
      assert mt[1].isSubset(midTriple[1]);
      assert mt[2].isSubset(midTriple[2]);
    }
    return midTriple;
  }

  XBitSet[] searchMidTriple(XBitSet[] mt, XBitSet separator) {
    if (nonExtendable(mt, separator)) {
      return null;
    }
    int v = unsettled(mt, separator);
    if (v == -1) {
      return mt;
    }
    if (countOccurrence(v, mt) == 1) {
      for (int i = 0; i < 3; i++) {
        if (!mt[i].get(v)) {
          XBitSet[] mt1 = addMT(mt, v, i);
          XBitSet[] mt2 = searchMidTriple(mt1, separator);
          if (mt2 != null) {
            return mt2;
          }
        }
      }
    }
    else {
      assert countOccurrence(v, mt) == 0;
      for (int i = 0; i < 3; i++) {
        XBitSet[] mt1 = mt;
        for (int j = 0; j < 3; j++) {
          if (j != i) {
            mt1 = addMT(mt1, v, j);
          }
        }
        XBitSet[] mt2 = searchMidTriple(mt1, separator);
        if (mt2 != null) {
          return mt2;
        }
      }
    }
    return null;
  }

  XBitSet[] addMT(XBitSet[] mt, int v, int i) {
    XBitSet[] mt1 = new XBitSet[3];
    for (int j = 0; j < 3; j++) {
      if (j == i) {
        mt1[j] = mt[j].addBit(v);
      }
      else {
        mt1[j] = mt[j];
      }
    }
    return mt1;
  }

  boolean nonExtendable(XBitSet[] mt, XBitSet separator) {
    return nonExtendable(mt, separator, k);
  }

  boolean nonExtendable(XBitSet[] mt, XBitSet separator, int k) {
    if (mt[0].cardinality() > k) return true;
    if (mt[1].cardinality() > k) return true;
    if (mt[2].cardinality() > k) return true;
    int ss = separator.cardinality();
    if ((mt[0].intersectWith(mt[1])).cardinality() + ss > 2 * k) {
      return true;
    }

    if ((mt[1].intersectWith(mt[2])).cardinality() + ss > 2 * k) {
      return true;
    }

    if ((mt[2].intersectWith(mt[0])).cardinality() + ss > 2 * k) {
      return true;
    }

    if (mt[0].intersectWith(mt[1].intersectWith(mt[2])).cardinality() + 2 * ss > 3 * k) {
      return true;
    }
    return false;
  }

  int unsettled(XBitSet[] mt, XBitSet separator) {
    for (int v: separator.toArray()) {
      if (countOccurrence(v, mt) == 1) {
        return v;
      }
    }
    for (int v: separator.toArray()) {
      if (countOccurrence(v, mt) == 0) {
        return v;
      }
    }
    return -1;
  }

  int countOccurrence(int v, XBitSet[] mt) {
    int count = 0;
    for (int i = 0; i < 3; i++) {
      if (mt[i].get(v)) {
        count++;
      }
    }
    return count;
  }


  XBitSet coreUnion(ArrayList<Block> blocks) {
    XBitSet union = new XBitSet();
    for (Block block: blocks) {
      union.or(block.core);
    }
    return union;
  }

  boolean isIndependent(XBitSet core) {
    for (int v: core.toArray()) {
      for (int w: core.toArray()) {
        if (v < w && g.areAdjacent(v, w)) {
          return false;
        }
      }
    }
    return true;
  }

  class BlockDerivation {
    Block block;
    ArrayList<Block> subblocks;
    XBitSet separator;
    XBitSet[] midTriple;

    BlockDerivation(Block block, ArrayList<Block> subblocks) {
      this.block = block;
      this.subblocks = subblocks;
      separator = block.vs.subtract(coreUnion(subblocks));
      if (TRACE_DERIVATION) {
        System.out.println("new derivation " + this);
        System.out.println("subblocks ..");
        for (Block b: subblocks) {
          System.out.println("   " + b);
        }
      }
    }

    void analyze() {
      System.out.println("analyzing k " + k + " " + this);
      System.out.println("  block boundary " + block.boundary);
      System.out.println("  separator " + separator);
      System.out.println("  " + subblocks.size() + " subblocks");
      for (Block sub: subblocks) {
        System.out.println("    " + sub);
      }
      System.out.println("  union bd " + unionBD(subblocks));
      System.out.println("  intersectin " + block.boundary.intersectWith(unionBD(subblocks)));
    }
    boolean isDerivationOf(Block block) {
      return this.block == block;
    }

    XBitSet unionBD(ArrayList<Block> blocks) {
      XBitSet union = new XBitSet();
      for (Block block: blocks) {
        union.or(block.boundary);
      }
      return union;
    }

    void verifyMidTriple(XBitSet[] mt) {
      for (int i = 0; i < 3; i++) {
        if (mt[i].cardinality() > k) {
          System.out.println("order exceeds k " + k + ", mt " + Arrays.toString(mt));
          assert false;
        }
        for (int u: separator.toArray()) {
          for (int v: separator.toArray()) {
            if (g.areAdjacent(u, v)) {
              if (!containedInSome(u, v, mt)) {
                System.out.println("not covered u " + u + " v " + v + ", mt " + Arrays.toString(mt));
              }
            }
          }
        }
      }
    }

    boolean containedInSome(int u, int v, XBitSet[] mt) {
      for (XBitSet m: mt) {
        if (m.get(u) && m.get(v)) {
          return true;
        }
      }
      return false;
    }

    void computeMidTriple() {
      if (separator.cardinality() > 3 * k / 2) {
        return;
      }
      if (subblocks.size() > separator.cardinality()) {
        //        System.out.println(subblocks.size() + " > " + separator.cardinality());
        midTriple = sepToMidTriple();
        if (midTriple != null) {
          assert midTriple[0].cardinality() <= k;
          assert midTriple[1].cardinality() <= k;
          assert midTriple[2].cardinality() <= k;
          assert midTriple[0].unionWith(midTriple[1]).equals(separator);
          assert midTriple[1].unionWith(midTriple[2]).equals(separator);
          assert midTriple[2].unionWith(midTriple[0]).equals(separator);
          for (Block block: subblocks) {
            assert block.boundary.isSubset(midTriple[0]) ||
            block.boundary.isSubset(midTriple[1]);
          }
        }
      }
      else {
        PartitionState state = new PartitionState();
        if (subblocks.size() > 0) {
          //          System.out.println("choose0(0) of state " + state);
          state = state.choose0(0);
          //          System.out.println(" ... " + state);
        }
        midTriple = state.search();
        if (midTriple != null) {
          assert midTriple[0].cardinality() <= k;
          assert midTriple[1].cardinality() <= k;
          assert midTriple[2].cardinality() <= k;
          assert midTriple[0].unionWith(midTriple[1]).equals(separator);
          assert midTriple[1].unionWith(midTriple[2]).equals(separator);
          assert midTriple[2].unionWith(midTriple[0]).equals(separator);
          for (Block block: subblocks) {
            assert block.boundary.isSubset(midTriple[0]) ||
            block.boundary.isSubset(midTriple[1]);
          }
        }
      }
    }

    XBitSet boundaryUnion(XBitSet part) {
      XBitSet bd = new XBitSet();
      for (int i: part.toArray()) {
        bd.or(subblocks.get(i).boundary);
      }
      return bd;
    }

    XBitSet[] sepToMidTriple() {
      if (TRACE_DERIVATION) {
        System.out.println("midTripe by separtor " + this);
      }

      int s = separator.cardinality();
      if (s <= k) {
        return new XBitSet[] {separator, new XBitSet(), separator};
      }
      int m = 2 * k - s;
      Set<XBitSet> intersections = subsetsUpTo(separator, m);
      for (XBitSet intersec: intersections) {
        XBitSet rest = separator.subtract(intersec);
        Set<XBitSet[]> bipartitions = bipartitionsUpto(rest, k - intersec.cardinality());
        for (XBitSet[] parts: bipartitions) {
          XBitSet mt2 = block.boundary.unionWith(parts[0]).unionWith(parts[1]);
          if (mt2.cardinality() > k) {
            continue;
          }
          XBitSet mt0 = intersec.unionWith(parts[0]);
          assert mt0.cardinality() <= k;
          XBitSet mt1 = intersec.unionWith(parts[1]);
          assert mt1.cardinality() <= k;
          boolean allAccounted = true;
          for (Block sub: subblocks) {
            if (!sub.boundary.isSubset(mt0) && !sub.boundary.isSubset(mt1)) {
              allAccounted = false;
              break;
            }
          }
          if (allAccounted) {
            XBitSet[] midTriple = new XBitSet[] {mt0, mt1, mt2};
            verifyMidTriple(midTriple);
            return midTriple;
          }
        }
      }
      return null;
    }

    Set<XBitSet[]> bipartitionsUpto(XBitSet s, int m) {
      Set<XBitSet[]> partitions = new HashSet<>();
      if (s.isEmpty()) {
        partitions.add(new XBitSet[] {new XBitSet(), new XBitSet()});
        return partitions;
      }
      if (s.cardinality() > 2 * m) {
        return partitions;
      }
      int i0 = s.cardinality() - m;
      for (int i = i0; i <= s.cardinality() / 2; i++) {
        Set<XBitSet> subsets = subsets(s, i);
        for (XBitSet s1: subsets) {
          XBitSet s2 = s.subtract(s1);
          if (s2.cardinality() > m)
            if (XBitSet.cardinalityComparator.compare(s1, s2) < 0) {
              partitions.add(new XBitSet[] {s1, s2});
            }
        }
      }
      return partitions;   
    }

    BDNode toBD(BranchDec bdec, Set<XBitSet> remainingEdges) {  
      assert midTriple != null;

      if (isIndependent(block.core) && block.boundary.cardinality() == 1) {
        return bdec.bdOfEdgesBetween(block.boundary, block.core, remainingEdges);
      }

      ArrayList<Block> subblocks0 = new ArrayList<>();
      ArrayList<Block> subblocks1 = new ArrayList<>();
      for (Block sub: subblocks) {
        if (sub.boundary.isSubset(midTriple[0])) {
          subblocks0.add(sub);
        }
        else {
          assert sub.boundary.isSubset(midTriple[1]);
          subblocks1.add(sub);
        }
      }

      BDNode[] bd = new BDNode[2];
      bd[0] = toBD(subblocks0, bdec, remainingEdges);
      bd[1] = toBD(subblocks1, bdec, remainingEdges);

      BDNode bd0 = bdec.compose(bd[0], bdec.bdOfEdgesIn(midTriple[0], remainingEdges));
      BDNode bd1 = bdec.compose(bd[1], bdec.bdOfEdgesIn(midTriple[1], remainingEdges));

      BDNode bd2 = bdec.compose(bd0, bd1);
      BDNode bd3 = bdec.compose(bd2, bdec.bdOfEdgesIn(midTriple[2], remainingEdges));
      return bd3;
    }

    BDNode toBD(ArrayList<Block> blocks, BranchDec bdec, Set<XBitSet> remainingEdges) {
      BDNode bd1 = null;
      for (Block b: blocks) {
        BDNode bd2 = ((BlockDerivation) b.derivation).toBD(bdec, remainingEdges);
        bd1 = bdec.compose(bd1, bd2);
      }
      return bd1;
    }

    boolean isBasic() {
      return subblocks.isEmpty();
    }

    @Override
    public String toString() {
      return "block " + block + " separator " + separator + " midTriple: " + 
          Arrays.toString(midTriple) + 
          " subblocks: " + subblocks.size();
    }

    class PartitionState {
      XBitSet unchosen;
      XBitSet[] chosen;
      XBitSet[] mt;
      PartitionState(){
        unchosen = XBitSet.all(subblocks.size());
        chosen = new XBitSet[] {new XBitSet(), new XBitSet()};
        mt = new XBitSet[] {new XBitSet(), new XBitSet(), block.boundary};
      }

      PartitionState(XBitSet unchosen, XBitSet[] chosen, XBitSet[] mt) {
        this.unchosen = unchosen;
        this.chosen = chosen;
        this.mt = mt;
      }

      XBitSet[] search() {
        //        System.out.println("search ps " + this);
        if (infeasible()) {
          //          System.out.println("  ...infeasible ");
          return null;
        }
        if (unchosen.isEmpty()) {
          for (Block block: subblocks) {
            assert block.boundary.isSubset(mt[0]) ||
            block.boundary.isSubset(mt[1]);
          }
          XBitSet[] mt = fillFree();
          //          System.out.println("  .. returning fillFrees " + Arrays.toString(mt));
          return mt;
        }
        for (int i: unchosen.toArray()) {
          PartitionState s0 = choose0(i);
          PartitionState s1 = choose1(i);
          if (s0.infeasible()) {
            return s1.search();

          }
          else if (s1.infeasible()) {
            return s0.search();
          }
        }
        int i = unchosen.nextSetBit(0);
        XBitSet[] mt = choose0(i).search();
        if (mt != null) {
          return mt;
        }
        return choose1(i).search();
      }

      XBitSet[] fillFree() {
        return searchMidTriple(mt);
      }

      boolean nonExtendable(XBitSet[] mt) {
        if (mt[0].cardinality() > k) return true;
        if (mt[1].cardinality() > k) return true;
        if (mt[2].cardinality() > k) return true;
        int ss = separator.cardinality();
        if ((mt[0].intersectWith(mt[1])).cardinality() + ss > 2 * k) {
          return true;
        }

        if ((mt[1].intersectWith(mt[2])).cardinality() + ss > 2 * k) {
          return true;
        }

        if ((mt[2].intersectWith(mt[0])).cardinality() + ss > 2 * k) {
          return true;
        }

        if (mt[0].intersectWith(mt[1].intersectWith(mt[2])).cardinality() + 2 * ss > 3 * k) {
          return true;
        }
        return false;
      }

      XBitSet[] searchMidTriple(XBitSet[] mt) {
        if (nonExtendable(mt)) {
          return null;
        }
        int v = unsettled(mt);
        if (v == -1) {
          return mt;
        }
        if (countOccurrence(v, mt) == 1) {
          for (int i = 0; i < 3; i++) {
            if (!mt[i].get(v)) {
              XBitSet[] mt1 = addMT(mt, v, i);
              XBitSet[] mt2 = searchMidTriple(mt1);
              if (mt2 != null) {
                return mt2;
              }
            }
          }
        }
        else {
          assert countOccurrence(v, mt) == 0;
          for (int i = 0; i < 3; i++) {
            XBitSet[] mt1 = mt;
            for (int j = 0; j < 3; j++) {
              if (j != i) {
                mt1 = addMT(mt1, v, j);
              }
            }
            XBitSet[] mt2 = searchMidTriple(mt1);
            if (mt2 != null) {
              return mt2;
            }
          }
        }
        return null;
      }

      XBitSet[] addMT(XBitSet[] mt, int v, int i) {
        XBitSet[] mt1 = new XBitSet[3];
        for (int j = 0; j < 3; j++) {
          if (j == i) {
            mt1[j] = mt[j].addBit(v);
          }
          else {
            mt1[j] = mt[j];
          }
        }
        return mt1;
      }

      int unsettled(XBitSet[] mt) {
        for (int v: separator.toArray()) {
          if (countOccurrence(v, mt) == 1) {
            return v;
          }
        }
        for (int v: separator.toArray()) {
          if (countOccurrence(v, mt) == 0) {
            return v;
          }
        }
        return -1;
      }

      int countOccurrence(int v, XBitSet[] mt) {
        int count = 0;
        for (int i = 0; i < 3; i++) {
          if (mt[i].get(v)) {
            count++;
          }
        }
        return count;
      }     
      boolean infeasible() {
        return mt[0].cardinality() > k ||    
            mt[1].cardinality() > k ||
            mt[2].cardinality() > k;
      }

      PartitionState choose0(int i) {
        assert !chosen[0].get(i);
        assert unchosen.get(i);
        XBitSet unchosen1 = unchosen.removeBit(i);
        XBitSet bdYet = unionBD(unchosen1);
        XBitSet[] mt1 = new XBitSet[3];
        XBitSet bd = subblocks.get(i).boundary;
        mt1[0] = mt[0].unionWith(bd);
        mt1[1] = mt[1];
        mt1[2] = mt[2];
        return new PartitionState(unchosen1, new XBitSet[] {chosen[0].removeBit(i), chosen[1]}, mt1);
      }

      PartitionState choose1(int i) {
        assert !chosen[1].get(i);
        assert unchosen.get(i);
        XBitSet unchosen1 = unchosen.removeBit(i);
        XBitSet bdYet = unionBD(unchosen1);
        XBitSet[] mt1 = new XBitSet[3];
        XBitSet bd = subblocks.get(i).boundary;
        mt1[0] = mt[0];
        mt1[1] = mt[1].unionWith(bd);
        mt1[2] = (XBitSet) mt[2].clone();
        return new PartitionState(unchosen1, new XBitSet[] {chosen[0], chosen[1].removeBit(i)}, mt1);
      }

      XBitSet unionBD(XBitSet sbInds) {
        XBitSet union = new XBitSet();
        for (int i: sbInds.toArray()) {
          union.or(subblocks.get(i).boundary);
        }
        return union;
      }

      public String toString() {
        return "unchosen " + unchosen + " chosen " + Arrays.toString(chosen) + 
            " mt " + Arrays.toString(mt);
      }

    }

  }

  class BlockTree {
    BTNode root;
    BlockTree(Set<Block> Blocks) {
      root = new BTNode(Blocks, new XBitSet(), 0);
    }

    int size() {
      return root.bag.size();
    }

    void add(Block b) {
      root.add(b);
    }

    class BTNode {
      Set<Block> bag;
      int d;
      XBitSet mask;
      XBitSet core;
      BTNode[] children;
      BTNode(Set<Block> Blocks, XBitSet core, int d) {
        this.core = core;
        this.d = d;
        mask = XBitSet.all(d * chunk).intersectWith(g.all);
        bag = new HashSet<>(Blocks);

        if (Blocks.size() <= MAX_BAG_SIZE) {
          return;
        }
        else {
          split();
        }
      }

      void collectSubblocks(XBitSet core1, Set<Block> Blocks) {
        if (!core.isSubset(core1)) {
          return;
        }
        if (children == null) {
          for (Block b: bag) {
            if (b.core.isSubset(core1)) {
              Blocks.add(b);
            }
          }
        }
        else {
          for (BTNode node: children) {
            node.collectSubblocks(core1, Blocks);
          }
        }
      }

      void split() {
        XBitSet mask1 = XBitSet.all(chunk * (d + 1));

        Map<XBitSet, Set<Block>> childMap = new HashMap<>();
        for (Block b: bag) {
          assert b.core.intersectWith(mask).equals(core);
          XBitSet core1 = b.core.intersectWith(mask1);
          Set<Block> bs = childMap.get(core1);
          if (bs == null) {
            bs = new HashSet<>();
            childMap.put(core1, bs);
          }
          bs.add(b);
        }
        children = new BTNode[childMap.size()];
        int i = 0;
        for (XBitSet c: childMap.keySet()) {
          children[i++] = new BTNode(childMap.get(c), c, d + 1);
        }
      }

      void add(Block b) {
        assert b.core.intersectWith(mask).equals(core);
        bag.add(b);
        if (bag.size() <= MAX_BAG_SIZE) {
          return;
        }
        if (children == null) {
          split();
        }
        else {
          XBitSet mask1 = XBitSet.all(chunk * (d + 1));
          XBitSet compo1 = b.core.intersectWith(mask1);
          boolean added = false;
          for (BTNode ch: children) {
            if (compo1.equals(ch.core)) {
              ch.add(b);
              added = true;
              break;
            }
          }
          if (!added) {
            int nc = children.length;
            children = Arrays.copyOf(children, nc + 1);
            Set<Block> cs = new HashSet<>();
            cs.add(b);
            children[nc] = new BTNode(cs, compo1, d + 1);
          }
        }
      }

      @Override
      public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("node d " + d + " core " + core + " bag " + bag.size());
        if (children != null) {
          sb.append(" children " + children.length);
        }
        return sb.toString();
      }

    }
  }

  class MscDT {
    MNode root;
    MscDT(Set<XBitSet> mscs) {
      root = new MNode(mscs, new XBitSet(), new XBitSet(), 0);
    }

    ArrayList<XBitSet> collectCombinables(XBitSet scope, XBitSet subsep) {
      ArrayList<XBitSet> combinables = new ArrayList<>();
      root.collectCombinables(scope, subsep, combinables);
      return combinables;
    }

    int size() {
      return root.bag.size();
    }

    void add(XBitSet c) {
      root.add(c);
    }

    class MNode {
      Set<XBitSet> bag;
      int d;
      XBitSet mask;
      XBitSet compoPart;
      XBitSet sepPart;
      MNode[] children;
      MNode(Set<XBitSet> mscs, XBitSet compoPart, XBitSet sepPart, int d) {
        this.sepPart = sepPart;
        this.compoPart = compoPart;
        this.d = d;
        mask = XBitSet.all(d * chunk).intersectWith(g.all);
        bag = new HashSet<>(mscs);

        if (mscs.size() <= MAX_BAG_SIZE) {
          return;
        }
        else {
          split();
        }
      }

      void collectCombinables(XBitSet scope, XBitSet subsep, ArrayList<XBitSet> combinables) {
        if (!compoPart.isSubset(scope)) {
          return;
        }
        if (sepPart.unionWith(subsep).cardinality() > k) {
          return;
        }
        if (children == null) {
          for (XBitSet c: bag) {
            if (c.isSubset(scope) &&
                g.neighborSet(c).unionWith(subsep).cardinality() <= k) {
              combinables.add(c);
            }
          }
        }
        else {
          for (MNode ch: children) {
            ch.collectCombinables(scope, subsep, combinables);
          }
        }
      }

      XBitSet vsPart() {
        return compoPart.unionWith(sepPart);
      }

      void split() {
        XBitSet mask1 = XBitSet.all(chunk * (d + 1));

        Map<CSPair, Set<XBitSet>> childMap = new HashMap<>();
        for (XBitSet c: bag) {
          assert c.intersectWith(mask).equals(compoPart);
          assert g.neighborSet(c).intersectWith(mask).equals(sepPart);
          XBitSet sep1 = g.neighborSet(c).intersectWith(mask1);
          XBitSet compo1 = c.intersectWith(mask1);
          CSPair cb = new CSPair(compo1, sep1);
          Set<XBitSet> cs = childMap.get(cb);
          if (cs == null) {
            cs = new HashSet<>();
            childMap.put(cb, cs);
          }
          cs.add(c);
        }
        children = new MNode[childMap.size()];
        int i = 0;
        for (CSPair cb: childMap.keySet()) {
          children[i++] = new MNode(childMap.get(cb), cb.vs, cb.sep, d + 1);
        }
      }

      void add(XBitSet c) {
        assert c.intersectWith(mask).equals(compoPart);
        assert g.neighborSet(c).intersectWith(mask).equals(sepPart);
        bag.add(c);
        if (bag.size() <= MAX_BAG_SIZE) {
          return;
        }
        if (children == null) {
          split();
        }
        else {
          XBitSet mask1 = XBitSet.all(chunk * (d + 1));
          XBitSet compo1 = c.intersectWith(mask1);
          XBitSet sep1 = g.neighborSet(c).intersectWith(mask1);
          boolean added = false;
          for (MNode ch: children) {
            if (compo1.equals(ch.compoPart) && sep1.equals(ch.sepPart)) {
              ch.add(c);
              added = true;
              break;
            }
          }
          if (!added) {
            int nc = children.length;
            children = Arrays.copyOf(children, nc + 1);
            Set<XBitSet> cs = new HashSet<>();
            cs.add(c);
            children[nc] = new MNode(cs, compo1, sep1, d + 1);
          }
        }
      }

      @Override
      public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("node d " + d + " compoPart " + compoPart + " sepPart " + sepPart + " bag " + bag.size());
        if (children != null) {
          sb.append(" children " + children.length);
        }
        return sb.toString();
      }

    }
  }

  static String spaces(int n) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i  < n; i++) {
      sb.append(" ");
    }
    return sb.toString();
  }


  static void debug(String path) {

  }

  static void test(String path, int k) {
    File file = new File(path);
    Graph g = Graph.readGraph(file);
    System.out.println(file.getName() + ": n " + 
        g.n + " m " + g.numberOfEdges());

    if (!g.isConnected(g.all)) {
      System.out.println("not connected");
    }

    g.printRaw(System.out);
    for (int d = 1; d < g.n; d++) {
      if (countDeg(d, g) > 0) {
        System.out.println("deg " + d + " " + countDeg(d, g));
      }
    }
    long t0 = System.currentTimeMillis();
    BlockDPWithoutRD0 cc = new BlockDPWithoutRD0(g);
    cc.decompose();
    long t1 = System.currentTimeMillis();
    assert cc.branchDec != null;
    System.out.println("branchwidth " + cc.k + " in " + (t1 - t0) + " milllisecs");    
  }

  static int countDeg(int d, Graph g) {
    int count = 0;
    for (int v = 0; v < g.n; v++) {
      if (g.neighborSet[v].cardinality() == d) {
        count++;
      }
    }
    return count;
  }

  public static void main(String[] args) {
    //        test("../instance/pace17exact/ex001.gr", 9);
    //            test("../instance/pace17exact/ex010.gr", 8);
    //            test("../instance/pace17exact/ex009.gr", 7);
    //        test("../instance/pace17exact/ex008.gr", 9);
    //                test("../instance/pace17exact/ex006.gr", 6);
    //            test("../instance/pace17exact/ex007.gr", 11);
    //    test("../instance/pace17exact/ex117.gr", 12);
    //    test("../instance/pace17exact/ex117.gr", 10);
    //          test("../instance/100/contiki_httpd-cfs_send_headers.gr", 4);
    //          test("../instance/100/contiki_httpd-cfs_send_file.gr", 4);
    //    test("../instance/100/contiki_shell-rime_recv_collect.gr", 3); // tw = 2 
    //                test("../instance/100/contiki_dhcpc_handle_dhcp.gr", 7);
    //        test("../instance/100/contiki_uip_uip_connect.gr", 4);
    //            test("../instance/100/FlowerSnark.gr", 6); // bw = 6
    //                        test("../instance/100/ShrikhandeGraph.gr", 8);// bw = 8
    //                            test("../instance/100/ClebschGraph.gr", 8);// bw = 8
    //    test("../instance/100/DyckGraph.gr", 8);// bw = 8
    //    debug("../instance/100/DyckGraph.gr");// bw = 8
    //                    test("../instance/100/fuzix_vfscanf_vfscanf.gr", 7);
    //              test1();
    //                    test("../instance/treewidthLib/HortonGrap.gr", 6);// bw = 6
    //    debug("../instance/treewidthLib/CoxeterGraph.gr");
    //            test("../instance/treewidthLib/F26AGraph.gr",7 );// bw = 7  
    //                            test("../instance/treewidthLib/BrinkmannGraph.gr",8 );// bw = 8 
    //            test("../instance/treewidthLib/MarkstroemGraph.gr",4 );// MarkstroemGraph.gr 24  4 123
    //                                        test("../instance/treewidthLib/RobertsonGraph.gr",8); // RobertsonGraph.gr  19  8 118824
    //                test("../instance/treewidthLib/CompleteGraph_15.gr",10 ); //CompleteGraph_15.gr 15  10  196603
    //                test("../instance/treewidthLib/WienerArayaGraph.gr",7 ); //WienerArayaGraph.gr 42  7 44654
    //                test("../instance/treewidthLib/ErreraGraph.gr", 6); // bw = 6
    //                    test("../instance/treewidthLib/FlowerSnark.gr", 6); // bw = 6
    //                test("../instance/treewidthLib/FolkmanGraph.gr", 6); // bw = 6
    //   
    //            test("../instance/treewidthLib/HoltGraph.gr", 9); // bw = 9

    //        test("../instance/treewidthLib/HeawoodGraph.gr", 5); // bw = 5
    //        test("../instance/treewidthLib/KittellGraph.gr", 6); // bw = 6
    //    test("../instance/treewidthLib/PaleyGraph_17.gr", 9); // bw = 10 
    //    test("../instance/treewidthLib/BalancedTree_3_5.gr", 0); 
    //    test("../instance/treewidthLib/NonisotropicUnitaryPolarGraph_3_3.gr", 0);
    //        test("../instance/treewidthLib/Klein7RegularGraph.gr", 13); // bw =  /
    //        test("../instance/treewidthLib/Klein3RegularGraph.gr", 0); // bw =  /
    //             test("../instance/treewidthLib/TaylorTwographSRG_3.gr", 23); // tw = 22
    //            test("../instance/treewidthLib/HoffmanSingletonGraph.gr", 0); // bw = 
    //        test("../instance/treewidthLib/BarbellGraph_10_5.gr", 0); // bw = 
    //            test("../instance/treewidthLib/RingedTree_6.gr", 0); // bw = 
    //                test("../instance/treewidthLib/OddGraph_4.gr", 12); // tw = 12
    //    test("../instance/treewidthLib/OddGraph_5.gr", 0); 
    //            test("../instance/treewidthLib/LjubljanaGraph.gr", 13); // tw = 12
    //                                test("../instance/treewidthLib/SylvesterGraph.gr", 15); // tw = 15
    //         test("../instance/treewidthLib/CoxeterGraph.gr",7 );// bw = 7   
    //    test("../instance/treewidthLib/LadderGraph_20.gr", 0);// bw = 2   
    //    test("../instance/treewidthLib/GoethalsSeidelGraph_2_3.gr",0 );//    
    //    test("../instance/treewidthLib/PasechnikGraph_2.gr",0 );//    
    //    test("../instance/treewidthLib/BuckyBall.gr",0 );//    
    //    test("../instance/treewidthLib/BubbleSortGraph_5.gr",0 );//    
    //        test("../instance/treewidthLib/FosterGraph.gr",0 );//    
    //        test("../instance/treewidthLib/BiggsSmithGraph.gr",0 );//    
    //        test("../instance/treewidthLib/Tutte12Cage.gr",0 );//    
    //    test("../instance/treewidthLib/NStarGraph_5.gr",0 );//    
    //    test("../instance/treewidthLib/HigmanSimsGraph.gr",0 );//    
    //        test("../instance/treewidthLib/HarriesWongGraph.gr",0 );//    
    //        test("../instance/treewidthLib/NKStarGraph_8_2.gr",0 );//    
    //    test("../instance/treewidthLib/NKStarGraph_5_3.gr",0 );//    
    //    test("../instance/treewidthLib/HanoiTowerGraph_4_3.gr",0 );//    
    //    test("../instance/treewidthLib/DorogovtsevGoltsevMendesGraphGrayGraph.gr",0 );//    
    //    test("../instance/treewidthLib/DorogovtsevGoltsevMendesGraph.gr",0 );//    
    //    test("../instance/treewidthLib/HigmanSimsGraph.gr",0 );//  
    //        test("../instance/treewidthLib/KneserGraph_8_3.gr", 18);//
    //    test("../instance/treewidthLib/StarGraph_100.gr", 0);// 
    //    test("../instance/treewidthLib/CompleteBipartiteGraph_25_20.gr", 0);
    //        test("../instance/treewidthLib/HyperStarGraph_10_2.gr", 0);
    //        test("../instance/treewidthLib/FoldedCubeGraph_7.gr", 0);
    //    test("../instance/treewidthLib/Balaban10Cage.gr", 0);
    //    test("../instance/treewidthLib/M22Graph.gr", 0);
    //    //    test("../instance/treewidthLib/KneserGraph_8_3.gr", 19);//  
    //    //    test("../instance/treewidthLib/KneserGraph_8_3.gr", 20);//  
    //    //    test("../instance/treewidthLib/KneserGraph_8_3.gr", 21);//  
    //  test("../instance/treewidthLib/KneserGraph_10_2.gr", 0);//  
    //        test("../instance/treewidthLib/SymplecticDualPolarGraph_4_3.gr", 23);//  
    //    test("../instance/treewidthLib/SimsGewirtzGraph.gr",0 );//  
    //    test("../instance/treewidthLib/TetrahedralGraph.gr", 0);    
    //        test("../instance/treewidthLib/CubeGraph_6.gr",0 );//  
    //    test("../instance/treewidthLib/SquaredSkewHadamardMatrixGraph_2.gr",0 );//  
//    test("../instance/treewidthLib/FriendshipGraph_10.gr",0 );// 
//    test("test/resources/TetrahedralGraph.gr",0 );// 
    test("debugInst.gr", 0);
    //
  }
}

//