package experiment;

import tw.common.Graph;
import tw.common.TreeDecomposition;
import tw.decomposer.SemiPID;

public class Work {

  public static void main(String[] args) {
    Graph g = new Graph(9);
    g.addEdge(0, 1);
    g.addEdge(1, 2);
    g.addEdge(2, 3);
    g.addEdge(3, 4);
    g.addEdge(4, 5);
    g.addEdge(5, 6);
    g.addEdge(0, 6);
    g.addEdge(1, 6);
    g.addEdge(2, 7);
    g.addEdge(4, 7);
    g.addEdge(5, 7);
    g.addEdge(6, 7);
    g.addEdge(3, 8);
    g.addEdge(7, 8);
    
    TreeDecomposition td = SemiPID.decompose(g);
    td.save("./work.td");
        
  }

}
