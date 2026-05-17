package calc;

public class Calc {
  static double log23 = Math.log(3)/Math.log(2);
  public static void main(String[] args) {
    //    double p = 1.0 / 3.0;
    //    System.out.println(choose(1, p) + " " + choose(1 - p, p) + 
    //        " " + (choose(1, p) + choose(1 - p, p)) + " " + log23);
    calc8();
  }

  static void calc8() {
    double worst = 0;

    for (int ik = 1; ik < 666; ik++) {
      double k = toDouble(ik);
      for (int is = ik; is < k * 3000 / 2; is+=10) {
        double s = toDouble(is);
        double p = worstFor(k, s);

        if (p > worst) {
          worst = p;
          System.out.println("   new worst " + worst  + " k " + k + " s " + s);
        }
      }
    }
  }


  static double worstPower(double s, double c) {
    double worst = 0;
    for (int inc1 = 0; inc1 < c * 1000; inc1+= 10) {
      double nc1 = toDouble(inc1);
      for (int inc2 = 0; inc2 < (c - nc1) * 1000 / 2; inc2+= 10) {
        double nc2 = toDouble(inc2);
        double r = c - nc1 - nc2 * 2;
        assert r >= 0;

        double p1 = Math.pow(17 / 27, nc1) *
            Math.pow(43 / 81, nc2) *
            Math.pow(3.0, s);
        double p2 = Math.pow(2,  nc1 + nc2 + r / 3);
        //        System.out.println("s " + s + " nc1 " + nc1 +
        //            " nc2 " + nc2 + " r " + r + " p1 " + p1 + " p2 " + p2);
        double p = Math.min(p1, p2);
        if (p > worst) {
          worst = p;
        }
      }
    }

    return worst;
  }


  static double worstFor(double k, double s) {
    double worst = 0;
    for (int ia = 1; ia < 1000; ia += 50) {
      double a = toDouble(ia);
      for (int ib = 1; ib < Math.min(ia, k * 1000);ib += 50) {
        double b = toDouble(ib);
        assert b <= k;
        if (a <= s) {
          continue;
        }
        if (b > k) {
          continue;
        }
        if (a - b <= 1 - a || a - b <= 2.0 / 3.0 - s / 3) 
        {
          double m = 2 * k - s;

          double e0 = Math.min(choose(1, a), choose(a, b));
          double e1 = choose(a - b, s - b);
          double e2 = Math.min(a - s,
              choose(s, m));
          double p = Math.pow(2.0, e0 + e1 + e2);
          System.out.println("    k " +  " s " + s + 
              " a " + a + " b " + b + " m " + m + 
              " e0 " + e0 + " e1 " + e1 + " e2 " + e2 + " p " + p + 
              " choose " + choose(s, m));

          if (p > worst) {
            worst = p;
            System.out.println("    worst " + worst + " for k " + k + " s " + s + " at " + m);
          }
        }
      }
    }
    return worst;
  }

  static void calc7() {
    for (int ik= 5; ik < 66666; ik += 1) {
      double k = toDouble(ik, 100000);
      double sp = smallPartial1(k);
      double ls = largeSep(k);
      if (sp < ls) {
        System.out.println("k " + k + " small partial " + sp);
        System.out.println("            large sep " + ls);  
      }
      else {
        System.out.println("k " + k + " large sep " + ls);  
        System.out.println("            small partial " + sp);
      }


    }
  }

  static void calc6() {
    for (int ik= 5; ik < 66666; ik += 5) {
      double k = toDouble(ik, 100000);
      double central = central(k);
      double small = smallPartial(k);
      double profile = profile(k);
      System.out.println(k + " : " + k + " s " + (k * 3 / 2));
      double cs = Math.max(central, small);
      if (cs < profile) {
        System.out.println("   cs " + cs + " central " + central + " small " + small);
        System.out.println("   profile " + profile);
      }
      else {
        System.out.println("   profile " + profile);
        System.out.println("   cs " + cs + " central " + central + " small " + small);
      }
    }
  }

  static double central(double k) {
    double s = k * 3 / 2;
    double ex = choose(1, s) + 2 * s;
    return Math.pow(2.0, ex);
  }


  static double smallPartial(double k) {
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
        double e0 = choose(a, b);
        for (int ic = 1; ic < ia - ib; ic += 10) {
          double c = toDouble(ic);
          if (a - c > s) {
            continue;
          } 
          double e = e0 + choose(a - b, c) + 
              log23 * (a - c);
          //              2 * (a - c);

          double p = Math.pow(2, e);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            cWorst = c;
            eWorst = e;

          }
        }

      }
    }
    //    System.out.println("                                           worst " + worst + " for k " + k + " e " + eWorst + "a " + aWorst +
    //        " b " + bWorst + " c " + cWorst + " choice " + choice);   
    return worst;
  }

  static double smallPartial1(double k) {
    double s = 3 * k / 2;
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;
    for (int ia = 1; ia < 1000; ia += 10) {
      double a = toDouble(ia);
      for (int ib = 1; ib < k * 1000; ib += 10) {
        double b = toDouble(ib);
        //        System.out.println(" k " + k + " a " + a + " b " + b);
        if (a - b < 1 - a || a - b <= 0.5) {
          //        if (a - b <= 0.5) {
          double d = a - b - (k - b) / 2;
          if(d > 2.0 / 3.0) {
            continue;
          }
          double e1 = choose(a, b) + a * log23;
          double e2 = 0;
          double worstC = 0;
          for (int ic = 1; ic <= ia - ib; ic += 10) {
            double c = toDouble(ic);
            double e3 = choose(a, b) + choose(a - b, c) + (a - b);
            //(a - b) * log23;
            if (e3 > e2) {
              e2 = e3;
              worstC = c;
            }
          }
          double e = Math.min(e1, e2);
          double p = Math.pow(2, e);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            eWorst = e;

          }
        }

      }
    }
    System.out.println("                                           worst " + worst + " for k " + k + " e " + eWorst + "a " + aWorst +
        " b " + bWorst);   
    return worst;

  }

  static double largeSep(double k) {
    double s = 3 * k / 2;

    double e = choose(1, s) + (1 - s) * log23;

    double p = Math.pow(2, e);

    return p;
  }

  static double profile(double k) {
    double s = k * 3 / 2;
    double ex = choose(1, s) + log23 * (1 - s); 
    return Math.pow(2.0, ex);
  }

  static void calc5() {
    for (int ik= 1; ik < 6666; ik++) {
      double k = toDouble(ik, 10000);
      double s = k * 3 / 2;
      System.out.println(k + " : " + s + "  " +
          Math.pow(2,  choose(1, s) + 2 * s) + " " +
          Math.pow(2,  choose(1, s) + log23 * (1 - s)));
    }
  }

  static void calc4() {
    for (int is = 1000; is < 1500; is++) {
      double s = toDouble(is);
      System.out.println("s " + s);

      for (int ii = 0; ii < 1000; ii++) {
        double i = toDouble(ii);
        if (ii == 0) {
          System.out.println("   0.000: " + cover3(s, 1));
        }
        else {
          System.out.println("   " + i + ": " + (choose(1, i) + 
              cover3(s - i, 1 - i)));
        }
      }
    }
  }

  static double cover3(double s, double k) {
    return partition3(s, s / 3, s / 3, s / 3);
  }
  static void calc3() {
    for (int ik = 10; ik <= 670; ik += 10) {
      double k = toDouble(ik);
      double worst = 0.0;
      double sWorst = 0.0;
      for (int is = 10; is <= (3 * ik) / 2; is += 10) {
        double s = toDouble(is);
        double relevant = relevant(k, s);
        //       System.out.println("   cent " + cent + " k " + k + " s " + s);
        if (relevant > worst) {
          worst = relevant;
          sWorst = s;
        }
      }
      System.out.println("relevant for k " + k + " " + worst + " at s " + sWorst);
      double small = small(k);
      System.out.println("small for k " + k + " " + small); 
      double s = k * 3 / 2;
      System.out.println("profile for k " + k + " " + Math.pow(2.0, choose(1, s) + log23 * (1 - s)));
    }
  }

  static void calc2() {
    for (int ik = 10; ik <= 670; ik += 10) {
      double k = toDouble(ik);
      double worst = 0.0;
      double sWorst = 0.0;
      for (int is = 10; is <= (3 * ik) / 2; is += 1) {
        double s = toDouble(is);
        double cent = central(k, s);
        //        System.out.println("   cent " + cent + " k " + k + " s " + s);
        if (cent > worst) {
          worst = cent;
          sWorst = s;
        }
      }
      System.out.println("cent for k " + k + " " + worst + " at s " + sWorst);
    }
  }

  static void calc1() {
    double worst = 0.0;
    for (int ik = 1; ik <= 666; ik += 50) {
      double k = toDouble(ik);
      for (int is = 1; is <= (3 * ik) / 2; is += 50) {
        double s = toDouble(is);
        double cent = central(k, s);
        //        System.out.println("cent " + cent + " k " + k + " s " + s);
        double rel = relevant(k, s);
        double small = small(k);

        double opt1 = Math.max(cent, small);
        if (opt1 > worst) {
          System.out.println("  bad opt1  at k " + k + " s " + s);
          System.out.println("  opt1 " + opt1 + " cent " + cent + " small " + small);
        }
        if (Math.min(rel, opt1) > worst) {
          worst = Math.min(rel, opt1);
          System.out.println("new worst " + worst + " at k " + k + " s " + s);
          System.out.println("  opt1 " + opt1 + " cent " + cent + " small " + small);
          System.out.println("  relevant  " + rel);
        }

      }
    }

  }

  static void calc() {
    double worst = 0.0;
    for (int ik = 1; ik <= 666; ik += 1) {
      double k = toDouble(ik);
      for (int is = 1; is <= (3 * ik) / 2; is += 1) {
        double s = toDouble(is);
        double cent = central(k, s);
        System.out.println("  central " + cent + " k " + k + " s " + s);
        if (cent > worst) {
          worst = cent;
          System.out.println("new worst " + worst + " k " + k + " s " + s);
        }
      }
    }
  }

  static double  central(double k, double s) {
    double p = Math.pow(2.0, choose(1, s) + 2.0 * s);
    return p;
  }

  static double  central1(double k, double s) {
    double p = Math.pow(2.0, choose(1, s) + 
        //        bicover(s, k));
        Math.min(bicover(s, k), log23 * (1 - s)));
    return p;
  }

  static double bicover(double s, double k) {
    double max = 0;
    for (int ip1 = 1; ip1 <= k * 1000; ip1+= 50) {
      double p1 = toDouble(ip1);
      for (int ip2 = 1; ip2 <= k * 1000; ip2+= 50) {
        double p2 = toDouble(ip2);
        if (p1 + p2 > k) {
          continue;
        }

        double p3 = s - p1 - p2;
        if (p1 + p3 > k) {
          continue;
        }
        double e = partition3(s, p1, p2, p3);
        if (e > max) {
          max = e;
        }
      }
    }
    return max;
  }

  static double bicover2(double s, double k) {
    double max = 0;
    for (int ib1 = 1; ib1 <= k * 1000; ib1+= 10) {
      double b1 = toDouble(ib1);
      for (int ib2 = 1; ib2 <= k * 1000; ib2+= 10) {
        double b2 = toDouble(ib2);
        if (b1 > k) {
          continue;
        }
        if (b2 > k) {
          continue;
        }
        if (b1 + b2 < s) {
          continue;
        }
        double i = b1 + b2 - s;
        if ((b1 - i) + (b2 - i) > k) {
          continue;
        }
        double e = partition3(s, b1 - i, b2 - i, i);
        if (e > max) {
          max = e;
        }
      }
    }
    return max;
  }

  static double partition3(double s, double x1, double x2, double x3) {
    assert nearEnough(s, x1 + x2 + x3): s + " " + (x1 + x2 + x3);
    return choose(s, x1) + choose (s - x1, x2);
  }

  static double partition(double s, double x1, double x2, double x3, double x4) {
    assert nearEnough(s, x1 + x2 + x3 + x4): s + " " + (x1 + x2 + x3 + x4);
    return choose(s, x1) + choose (s - x1, x2) + choose (s - x1 - x2, x3) +
        choose(s - x1 - x2 - x3, x4);
  }

  static boolean nearEnough(double x, double y) {
    return Math.abs(x - y) < 1.0e-10;
  }

  static double relevant(double k, double s) {
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;

    for (int ia = 1; ia < 1000; ia += 10) {
      double a = toDouble(ia);
      if (a > 2.0 / 3.0 + k) {
        continue;
      }

      for (int ib = 1; ib < ia; ib += 10) {
        double b = toDouble(ib);
        if (b > k) {
          continue;
        }
        if (a - b > 1 - a && 
            a - b > 2.0 / 3.0 ) {
          continue;
        }
        double e0 = Math.min(choose(1, a), choose(a, b));
        for (int ic = 1; ic < ia - ib; ic += 10) {
          double c = toDouble(ic);
          if (a - c > s) {
            continue;
          }
          //          double e = e0 + choose(a - b, c) + bicover(a - c, k);
          double e = e0 + choose(a - b, c) + log23 * (a - c);

          double p = Math.pow(2, e);
          //          System.out.println(k + " " + a + " " + b + " " + c + " " + e1 + " " + e1 + " " + p);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            cWorst = c;
            eWorst = e;
          }
        }

      }
    }
    //    System.out.println("                                          worst " + worst + " for k " + k + " e " + eWorst + " a " + aWorst +
    //        " b " + bWorst + " c " + cWorst );   
    return worst;
  }

  static double relevant2(double k, double s) {
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;
    String choice = null;

    for (int ia = 1; ia < 1000; ia += 50) {
      double a = toDouble(ia);
      for (int ib = 1; ib < ia; ib += 50) {
        double b = toDouble(ib);
        if (b > k) {
          continue;
        }
        if (a - b > 1 - a &&
            a > 2.0 / 3.0 + s / 3) {
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
              Math.min(log23 * (a - b - c) + b + c, bicover(a - c, k));
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
      if (a > (1 + k) / 2) {
        continue;
      }
      for (int ib = 1; ib < k * 1000; ib += 10) {
        double b = toDouble(ib);
        double e0 = Math.min(choose(1, a), choose(a, b));
        for (int ic = 1; ic < ia - ib; ic += 10) {
          double c = toDouble(ic);
          if (a - c > s) {
            continue;
          } 
          double e = e0 + log23 * (a - c);
          double p = Math.pow(2, e);
          if (p > worst) {
            worst = p;
            aWorst = a;
            bWorst = b;
            cWorst = c;
            eWorst = e;
          }
        }

      }
    }
    System.out.println("                                           worst " + worst + " for k " + k + " e " + eWorst + "a " + aWorst +
        " b " + bWorst + " c " + cWorst);   
    return worst;

  }

  static double small1(double k) {
    double s = 3 * k / 2;
    double worst = 0;
    double aWorst = 0;
    double bWorst = 0;
    double cWorst = 0;
    double eWorst = 0;
    String choice = null;

    for (int ia = 1; ia < 1000; ia += 50) {
      double a = toDouble(ia);
      for (int ib = 1; ib < k * 1000; ib += 50) {
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
    if (a == 0 || a == b) {
      return 0;
    }
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
