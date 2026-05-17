package experiment;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Calendar;

public class MakeBatchFile {
//  static String group = "PACE2017bonus_gr";
  static int timeout = 1200;
//  static String group = "random";
  static String instancePath = ".." + File.separator + "instance"
   + File.separator + "treeWidthLib";
  static String batchFilePath = "bw_twLib2.sh";
  static String javaPath = "bw.BranchWidth"; 
  static String date;
  static String logFile;
  static String timeFile;

  public static void main(String[] args) {
    Calendar cl = Calendar.getInstance();

    String date = cl.get(Calendar.YEAR) + "_" + (cl.get(Calendar.MONTH) + 1)  + "_" + 
        cl.get(Calendar.DATE); 
    logFile = "log" + File.separator + "log_" + date;
    timeFile = "time" + File.separator + "time_" + date;
    
    File dir = new File(instancePath);
    File[] files = dir.listFiles();
    
    PrintStream ps = null;
    try {
      ps = new PrintStream(new FileOutputStream(batchFilePath));
      for (File file: files) {
        String name = file.getName();
        if (file.getName().endsWith(".gr")) {
          addLine(ps, name);
        }
      }
      ps.close();
    } catch (FileNotFoundException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }
  }

  static String toDigits(int i, int n) {
    String s = Integer.toString(i);
    while (s.length() < 3) {
      s = "0" + s;
    }
    return s;
  }

  static void addLine(PrintStream ps, String name) {
    ps.println("gtimeout " + timeout + " " + 
        "java -Xmx144g -Xss10m -classpath bin " + javaPath
//        "java -Xmx60g -Xss10m -classpath bin " + javaPath
    + " " + instancePath + File.separator + name);
  }
}
