package calc;

public class Isolater {
  static double log23 = Math.log(3)/Math.log(2);
  static double d;
  static double parts;
  public static void main(String[] args) {
    calc();
    //    recurrence();
  }
  static void calc() {
    d = 3.540;
    System.out.println("d = " + d + ",  2 ^ (d / 2) = " + Math.pow(2, d / 2));
    parts = 10.0;
    for (int is = 1; is <= 100; is++) {
      double s = toDouble(is, 100);
      double[] x = isolater(s);
      if (x != null) {
      System.out.println("best for s " + s + " q " + x[0] + " a " + x[1] + " e " + x[2]);
      }
    }    
  } 
  
  static double toDouble(int a, int n) {
    return ((double) a) / (double) (n);
  }
    
  
  static double[] isolater(double s) {
    double[] best = null;
    for (int ia = 1; ia < (1 - s) * 100; ia++) {
      double a = toDouble(ia, 100);
      double mu1 = a * d;
      double b = 1 - a - s;
      for (int ie = 1; ie < 100 * mu1; ie++) {
        double e = toDouble(ie, 100);  
        double delta1 = (mu1 - e) / mu1;
        double p1 = chernoffMinus(mu1, delta1);
        
        double mu2 = (d - e) * s / b;

        double delta2 = (e - mu2) / mu2;
        
        double p2 = chernoffPlus(mu2, delta2);
        double p = Math.max(p1, p2);
        double q1 = p * Math.pow(parts, (1 - s)); 
        double q2 = Math.pow(parts, a + (1 - a - s) / 2);
        double q = Math.max(q1, q2);
        if (best == null || q < best[0]) {
          System.out.println(" new best s " + s +
              " q " + q + " q1 " + q1 + " q2 " + q2 + " p " + p + " p1 " + p1 + 
              " p2 " + p2 + " a " + a + " e " + e);
          best = new double[] {q, a, e};
        }
      }
           
    }
    return best;
  }
  
  static double chernoffMinus(double mu, double delta) {
    return Math.pow(Math.pow(Math.E, -delta)/ Math.pow(1 - delta, 1 - delta), mu);
  }
  
  static double chernoffPlus(double mu, double delta) {
    return Math.pow(Math.pow(Math.E, delta)/ Math.pow(1 + delta, 1 + delta), mu);
  }
}
