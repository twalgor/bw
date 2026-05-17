package tw.minseps;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import tw.common.Graph;
import tw.common.XBitSet;

public class Berry {
  Graph g;

  public Set<XBitSet> minSeps;
  Queue<XBitSet> toProcess = new LinkedList<>();

  public Berry(Graph g) {
    this.g = g;
  }

  public void generate() {
    minSeps = new HashSet<>();
    for (int v = 0; v < g.n; v++) {
      XBitSet closure = g.neighborSet[v].addBit(v);
      ArrayList<XBitSet> components = g.separatedComponents(closure);
      for (XBitSet compo: components) {
        XBitSet sep = g.neighborSet(compo);
        if (!minSeps.contains(sep)) {
          minSeps.add(sep);
          toProcess.add(sep);
        }
      }
      while (!toProcess.isEmpty()) {
        XBitSet sep0 = toProcess.remove();
        for (int s: sep0.toArray()) {
          XBitSet sep1 = sep0.unionWith(g.neighborSet[s]);
          components = g.separatedComponents(sep1);
          for (XBitSet compo: components) {
            XBitSet sep = g.neighborSet(compo);
            if (!minSeps.contains(sep)) {
              minSeps.add(sep);
              toProcess.add(sep);
            }
          }
        }
      }
    }
  }
}
