package tw.common;

import java.util.Arrays;

public class Subgraph {
  Graph g;
  public XBitSet vertices;
  public int[] conv;
  public int[] inv;
  public Graph h;
  
  public Subgraph(Graph g, XBitSet vertices) {
    this.g = g;
    this.vertices = vertices;
    
    conv = new int[g.n];
    inv = new int[vertices.cardinality()];
    Arrays.fill(conv, -1);
    int w = 0;
    for (int v = vertices.nextSetBit(0); v >= 0; v = vertices.nextSetBit(v + 1)) {
      inv[w] = v;
      conv[v] = w++;
    }

    h = new Graph(w);
    h.inheritEdges(g, conv, inv);
  }
  
  public static int[] compose(int[] conv1, int[] conv2) {
    int[] result = new int[conv1.length];
    for (int v = 0; v < conv1.length; v++) {
      if (conv1[v] == -1) {
        result[v] = -1;
      }
      else {
        assert conv1[v] < conv2.length;
        result[v] = conv2[conv1[v]];
      }
    }
    return result;
  }

}
