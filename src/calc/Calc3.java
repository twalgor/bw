package calc;

public class Calc3 {
  static double log23 = Math.log(3)/Math.log(2);
  public static void main(String[] args) {

    calc();
  }


  static void calc() {
    double worst = 0.0;
    for (int ik = 1; ik <= 666; ik += 50) {
      double k = toDouble(ik);
      for (int is = 1; is <= (3 * ik) / 2; is += 50) {
        double s = toDouble(is);
        for (int ib2 = 1; ib2 < is; ib2+= 10) {
          double b2 = toDouble(ib2);
          double cent = central(k, s, b2);
          System.out.println("cent " + cent + " k " + k + " s " + s + " b2 " + b2);
            double rel = relevant(k, s, b2);
            double small = small(k);

            double opt1 = Math.max(cent, small);
            if (Math.min(rel, opt1) > worst) {
              worst = Math.min(rel, opt1);
              System.out.println("new worst " + worst + " at k " + k + " s " + " b2 " + b2);
              System.out.println("  opt1 " + opt1 + " cent " + cent + " small " + small);
              System.out.println("  relevant  " + rel);
            }
        }
      }
    }
  }


  static double  central(double k, double s, double b2) {
    double p = Math.pow(2.0, choose(1, s) + tricover(s, k, b2));
    return p;
  }

  static double tricover(double s, double k, double b2) {
    double max = 0;
    for (int ib1 = 1; ib1 <= b2 * 1000; ib1++) {
      double b1 = toDouble(ib1);
      if (b1 + b2 + k < s) {
        continue;
      }
      for (int ib3 = 1; ib3 <= k * 1000; ib3++) {
        double b3 = toDouble(ib3);
        if (b1 + b2 + b3 < s) {
          continue;
        }
        double r = b1 + b2 + b3 - s;
        for (int ii3 = 0; ii3 <= r * 0.5 * 1000; ii3++) {
          double i3 = ii3;
          double r2 = r - i3 * 2;
          for (int ii12 = 0; ii12 < r2; ii12++) {
            double i12 = toDouble(ii12);
            double r3 = r2 - i12;
            for (int ii23 = 0; ii23 < r3; ii23++) {
              double i23 = toDouble(ii23);
              double i31 = r3 - i23;
              assert Math.pow(b1 + b2 + b3 - i12 - i23 - i31 - i3 - s, 2.0) < 0.000000001;
              double exclusive = s - i12 - i23 - i31 - i3;
              double ex1 = b1 - i12 - i31 - i3;
              double ex2 = b2 - i12 - i23 - i3;
              double ex3 = b3 - i23 - i31 - i3;
              assert Math.pow(ex1 + ex2 + ex3 + i12 + i23 + i31 + i3 - s, 2.0) < 0.000000001;
              assert Math.pow(ex1 + ex2 + ex3 -exclusive, 2.0) < 0.000000001;
              double e = choose(s, i3) +
                  choose(s - i3, i12) + choose(s - i3, i12) +
                  choose(s - i3 - i12, i23) + choose(s - i3 - i12 - i23, i31) + 
                  choose(exclusive, ex1) +
                  choose(exclusive - ex1, ex2);
              if  (e > max) {
                max = e;
              }
            }
          }
        }
      }
    }
    return max;
  }

  static double relevant(double k, double s, double b2) {
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;
    String choice = null;

    for (int ia = 1; ia < 1000; ia += 10) {
      double a = toDouble(ia);
      for (int ib = 1; ib < ia; ib += 10) {
        double b = toDouble(ib);
        if (b > k) {
          continue;
        }
        if (a - b > 1 - a &&
            a > 2.0 / 3.0 + k) {
          continue;
        }
        double e0 = Math.min(choose(1, a), choose(a, b));
        for (int ic = 1; ic < ia - ib; ic += 10) {
          double c = toDouble(ic);
          if (a - c > s) {
            continue;
          }
          double e1 = e0 + log23 * a;
          double e2 = e0 + choose(a - b, c) + 
              Math.min(log23 * (a - b - c) + b + c, log23 * (a - c));
          double e = Math.min(e1, e2);
          double p = Math.pow(2, e);
          //          System.out.println(k + " " + a + " " + b + " " + c + " " + e1 + " " + e1 + " " + p);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            cWorst = c;
            eWorst = e;
            if (e == e1) {
              choice = "first";
            }
            else {
              choice = "second";
            }
          }
        }

      }
    }
    System.out.println("                                          worst " + worst + " for k " + k + " e " + eWorst + " a " + aWorst +
        " b " + bWorst + " c " + cWorst + " choice " + choice);   
    return worst;
  }

  static double small(double k) {
    double s = 3 * k / 2;
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;
    String choice = null;

    for (int ia = 1; ia < 1000; ia += 10) {
      double a = toDouble(ia);
      for (int ib = 1; ib < k * 1000; ib += 10) {
        double b = toDouble(ib);
        if (a - b > 1 - a) {
          continue;
        }
        double e0 = Math.min(choose(1, a), choose(a, b));
        for (int ic = 1; ic < ia - ib; ic += 10) {
          double c = toDouble(ic);
          if (a - c > s) {
            continue;
          } 
          double e1 = e0 + log23 * a;
          double e2 = e0 + choose(a - b, c) + 
              Math.min(log23 * (a - b - c) + b + c, log23 * (a - c));

          double e = Math.min(e1, e2);
          double p = Math.pow(2, e);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            cWorst = c;
            eWorst = e;
            if (e == e1) {
              choice = "first";
            }
            else {
              choice = "second";
            }
          }
        }

      }
    }
    System.out.println("                                           worst " + worst + " for k " + k + " e " + eWorst + "a " + aWorst +
        " b " + bWorst + " c " + cWorst + " choice " + choice);   
    return worst;

  }

  static double choose(double a, double b) {
    return a * h(b / a);
  }
  static double c(double a, double b) {
    assert b < a;
    return Math.min(b, a * h(b / a));
  }

  static double toDouble(int a, int n) {
    return ((double) a) / (double) n;
  }
  static double toDouble(int a) {
    return toDouble(a, 1000);
  }

  static double h(double x) {
    return -x * log2(x) - (1 - x) * log2(1 - x);
  }

  static double log2(double x) {
    return Math.log(x) / Math.log(2.0);
  }
}
