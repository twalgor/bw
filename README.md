This repository contains implementations of algorithms to compute the branchwidth of a graph described in the following paper. 
```
@misc{kaneda2026fastpracticalsingleexponentialalgorithms,  
      title={Fast and Practical Single-Exponential Algorithms for Branchwidth},   
      author={Taiki Kaneda and Yasuaki Kobayashi and Hisao Tamaki},
      year={2026},  
      eprint={2605.17396},
      archivePrefix={arXiv},
      primaryClass={cs.DS},
      url={https://arxiv.org/abs/2605.17396}, 
}
```

The main purposes of this repository are to make the published experimental results reproducible and to make the code available for research use.  
If you use the code in this repository in your research and
publish results from that research, 
please cite this repository and/or the above paper.

## Building
Requirements: JDK 22 or newer  
The project targets Java 22 and uses no build tool. From the src directory: 
``` 
javac --release 22 -d ../bin bw/Algorithm1.java bw/Algorithm2.java  
```
javac automatically compiles all classes that Algorithm1 and Algorithm2 depend on. -d ../bin keeps the compiled .class files out of the source tree.

## Running
From the src directory:  
```
java -cp ../bin bw.Algorithm1 `<graph-file>`  [out-file]
java -cp ../bin bw.Algorithm2 `<graph-file>`  [out-file]
```
`<graph-file>` is the path to the input graph, in PACE .gr format. The path may be absolute or relative to the current directory. For example:  
```
java -cp ../bin bw.Algorithm1 ../instances/ex001.gr 
```
The first line in the standard output confirms that the graph file is read. Upon termination, a line describing the branchwidth and the time spent in milliseconds is written to the standard output.

If `<out-file>` is given as the second argument, the branch-decomposition computed is written in the file. The format is a full binary tree described by indentations, with ':' representing a non-leaf node and an edge description representing a leaf.  
For example  
```
:    
 :   
  2{0, 1}   
  :   
   2{0, 2}    
   2{1, 3}     
 :  
   2{0, 3}  
   2{2, 3}   
```
represents a binary tree with a root, two internal nodes at level 1, one internal node at level 2, and 5 leaves labeled by edges {0, 1}, {0, 2}, {1, 3}, {0, 3}, and {2, 3}. The number '2' prefixing the edge shows the cardinality of the edge, although our current algorithms are for graphs and therefore this number is always 2. The ternary tree corresponding to this full binary tree should be clear.  
**Note that the vertex number starts with 0, which is the internal representation in the implementation, and is the vertex number in the input file minus one in general.
