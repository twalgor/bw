package tw.decomposer;

import java.util.LinkedList;
import java.util.Set;

import tw.common.Graph;
import tw.common.TreeDecomposition;
import tw.common.XBitSet;
import tw.minseps.MinSepsGenerator;

public class ResourceBoundedSolver {
//  static final boolean TRACE = true;
  static final boolean TRACE = false;
  static final int REACH = 3;
  int nMinSeps;
  public int dpMax;
  Graph g;
  int k;
  Set<XBitSet> minSeps;
  SemiPID spid;
  
  public ResourceBoundedSolver(int nMinSeps, int initialDPMax) {
    this.nMinSeps = nMinSeps;
    dpMax = initialDPMax;
    if (TRACE) {
      System.out.println("Resource bounded solver created " + this);
    }
  }
  
  public boolean prepare(Graph g, int k, int extraDPSize) {
    this.g = g;
    this.k = k;
    
    if (TRACE) {
      System.out.println("preparing for " + g.n + " " + k + " " + this);
    }
    
    if (g.n > dpMax + extraDPSize + REACH) {
      if (TRACE) {
        System.out.println("rejected " + g.n);
      }
      return false;
    }

    MinSepsGenerator msg = new MinSepsGenerator(g, k);
    msg.generate();
    minSeps = msg.minSeps;
    if (g.n > dpMax && minSeps.size() <= nMinSeps) {
      dpMax = g.n;
    }
    return true;
  }

  public boolean isFeasible() {
    spid = new SemiPID(g, k, minSeps, false);
    boolean isFeasible = spid.isFeasible();
    if (TRACE) {
      System.out.println("isFeasible " + isFeasible);
    }
    return isFeasible;
  }
  
  public TreeDecomposition getTD() {
    return spid.getTD();
  }
  
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("nMinSep " + nMinSeps);
    sb.append(" dpMax " + dpMax);
    return sb.toString();
  }
 }
