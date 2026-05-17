package calc;

public class Calc1 {
  static double log23 = Math.log(3)/Math.log(2);
  public static void main(String[] args) {
//    System.out.println(Math.pow(2.0,  1.97));
    calc12();
    //    recurrence();
  }

  static void calc12() {
    double maxForK = 0.0;
    for (int ik = 1; ik <= 666; ik ++) {
      double k = toDouble(ik);
      System.out.println( " k = " + k + " choose(1, 3 * k / 2) " + choose(1, 3 * k / 2) + 
          " log_2 3 (1 - 3 * k / 2) " +
          log23 * (1 - 3 * k / 2));
      double v1 = Math.pow(2.0,  choose(1, 3 * k / 2) + log23 * (1 - 3 * k / 2));
      double max = 0.0;
      System.out.println("  option 1 value " + v1);
      for (int ia = 1; ia < 1000; ia += 10) {
        double a = toDouble(ia);
        for (int ib = 1; ib <= Math.min(ik, ia); ib+= 10) {
          double b = toDouble(ib);
          if (
              a > 0.5 * (1 + b) &&
//              a - b > 0.5 &&
              a + b > (2.0 / 3.0) * (1.0 + 3 * k / 2)) {
            continue;
          }
          for (int ic = ia - 3 * ik / 2; ic <=  ia - ib; ic++) {
            double c = toDouble(ic);

            double e1 = Math.min(choose(1, a), choose(a, b)) + 
                choose(a - b, c) + log23 * (a - b - c) + b + c;
            double e2 = Math.min(choose(1, a), choose(a, b)) + log23 * a;
            double e = Math.min(e1, e2);
            double v = Math.pow(2.0, e);
            if (v > max) {
              max = v;
              System.out.println("  new max " + max + " at k " + k + 
                  " e == e1 " + (e == e1) + " a " + a + " b " + b + " c " + c +
                  " log23 a " + log23 * a + 
                  " choose (1, a) " + choose(1, a) + " choose(a, b) " + choose(a, b) +
                  " choose (a - b, c) " + choose(a - b, c));

            }
          }
        }
        
      }
      double v = Math.min(v1, max);
      if (v > maxForK) {
        maxForK = v;
        System.out.println("new maxForK " + maxForK + " k " + k);
      }
    }
  }


  static void calc11() {
    double max = 0.0;
    for (int is = 1; is <= 666; is++) {
      double s = toDouble(is);
      double e1 = choose(1, s) + log23 * (1 - s);

      double e2 = 0.0;
      double aChosen = 0.0;
      double bChosen = 0.0;
      for (int ia = 1; ia < 1000; ia++) {
        double a = toDouble(ia);
        for (int ib = 1; ib < ia; ib++) {
          double b = toDouble(ib);

          //          if (a - b > Math.max(0.5, (1 - s) * 2.0 / 3.0)) {
          //            continue;
          //          }
          //          if (a > Math.max(b + (1 - s) * 2.0 / 3.0, (1 + s) / 2)) {
          //          if (a > Math.max(b + (1 - s) * 2.0 / 3.0, 0.5 + s / 3)) {
          if (a - b > Math.max((1 - b) / 2.0,  (2 + 4 * s )/ 3)) {      
            continue;
          }
          if (b > s * 2.0 / 3.0) {
            continue;
          }

          double e3 = Math.min(choose(1, a), choose(a, b)) + b + log23 * (a - b);
          //          double e4 = Math.min(choose(1, a), choose(a, b)) + b + 
          //              choose(a - b, s - b) + b + log23 * (s - b) + a - s;
          //          double e5 = Math.min(e3, e4);
          double e5 = e3;
          if (e5 > e2) {
            e2 = e5;
            aChosen = a;
            bChosen = b;
          }
        }
      }
      double e = Math.min(e1, e2);
      double v = Math.pow(2.0, e);
      if (v > max) {
        max = v;
        System.out.println("new max " + max + " e " +  e  + " s " + s + 
            " e1 " + e1 + " e2 " + e2);
        System.out.println( "e2 " + e2 + " achieved at a " + aChosen + " b " + bChosen + 
            " choose(1, a) " + choose(1, aChosen) + " choose(a, b) " + choose(aChosen, bChosen) + 
            " log23 * (a - b)) " + log23 * (aChosen - bChosen));
      }
    }
  }

  static void calc10() {
    double max = 0.0;
    for (int ia = 1; ia < 1000; ia++) {
      double a = toDouble(ia);
      for (int ib = 1; ib < ia; ib++) {
        double b = toDouble(ib);
        if (a - b > Math.max((1 - b) * 2.0 / 3.0, 0.5)) {
          continue;
        }
        if (a > 2 * (1 - a)) {
          continue;
        }
        double e = Math.min(choose(1, a), choose(a, b)) + b + log23 * (a - b);
        //        double e = choose(1, a) + log23 * (a - b);
        double v = Math.pow(2.0, e);
        if (v > max) {
          max = v;
          System.out.println("new max " + max + " e " +  e  + " at a " + a + " b " + b + 
              " choose(1, a) " + choose(1, a) + " choose(a, b) " + choose(a, b) + 
              " log23 * (a - b)) " + log23 * (a - b));
        }
      }
    }

  }

  static void calc8() {
    double max = 0.0;
    for (int ia = 1; ia < 1000; ia++) {
      double a = toDouble(ia);
      //      if (a > (7.0 / 6.0) * 2.0 / 3.0) {
      //        continue;
      //      }
      for (int ib = 1; ib < ia; ib++) {
        double b = toDouble(ib);
        if (a - b > Math.max((1 - b) * 2.0 / 3.0, 0.5)) {
          //        if (a - b > (1 - b) * 2.0 / 3.0) {
          continue;
        }
        double e = Math.min(choose(1, a), choose(a, b)) + b + log23 * (a - b);
        double v = Math.pow(2.0, e);
        if (v > max) {
          max = v;
          System.out.println("new max " + max + " e " +  e  + " at a " + a + " b " + b +
              " choose(1, a) " + choose(1, a) + " choose(a, b) " + choose(a, b) + "log_2 3(a - b) " + log23 * (a - b));
        }
      }
    }
  }

  static void calc7() {
    double max = 0.0;
    double kForMax = 0.0;
    double wsAtBest = 0.0;
    double waAtBest = 0.0;
    for (int ik = 1; ik < 66; ik++) {
      double k = toDouble(ik, 100);
      //      double k1 = k * 3 / 2;

      System.out.println("k " + k + " choose(1, k) " + choose(1, k) + " log_2 3((1- k) / 2) " + 
          log23 * ((1 - k) / 2) +
          " power of 2 " + Math.pow(2.0, choose(1, k) + log23 * ((1 - k) / 2)));
      double ws = worstSmall(k);
      double wa = worstAll(k);
      //      double x = Math.min(wa, Math.max(ws, choose(1, k) + log23*((1 - k) / 2)));
      double x = Math.min(wa, Math.max(ws, choose(1, k) + log23*(1 - k)));

      //      double x = wa;
      if (x > max) {
        System.out.println("new worst " + x + " at k " + k + " worstSmall " + ws + " worstAll " + wa + 
            //            " choose(1, k) " + choose(1, k) + " log_2 3((1 - k) / 2) " + log23*((1 - k) / 2));
            " choose(1, k) " + choose(1, k) + " log_2 3(1 - k) " + log23*(1 - k));
        max = x;
        kForMax = k;
        wsAtBest = ws;
        waAtBest = wa;
      }
    }
    System.out.println("max " + max + " power of 2 " + Math.pow(2.0, max) + " at k " + kForMax);
    System.out.println(" choose(1, 3k/2) " + choose(1, kForMax) + " log_2 3(1- k) " + log23 * (1 - kForMax));
    System.out.println(" wsAtBest " + wsAtBest + " waAtBset " + waAtBest);
    //    worstAll(kForMax);
  }

  static double worstSmall(double k) {
    double max = 0.0;
    for (int ia = 0; ia <= 1000; ia++) {
      double a = toDouble(ia);
      //      if (a - (1 - a) > k) {
      //        return max;
      //      }
      for (int ib = 0; ib <= ia; ib++) {
        double b = toDouble(ib);
        if (a - b > 0.5) {
          continue;
        }
        if (b > k) {
          break;
        }
        double v = b + (a - b) * log23;
        if (v > max) {
          System.out.println("  new worstSmall " + v + " at a " + a + " b " + b + " k " + k);
          max = v;
        }
      }
    }
    return max;
  }

  static double worstAll(double k) {
    double max = 0.0;
    for (int ia = 0; ia <= 1000; ia++) {
      double a = toDouble(ia);
      for (int ib = 0; ib <= ia; ib++) {
        double b = toDouble(ib);
        if (b > k) {
          break;
        }
        double c = Math.max(0, a - 3 * k / 2);
        double v = Math.min(choose(1, a), choose(a, b)) + 
            Math.min(choose(a- b, c) + b + c + (a - b - c) * log23, b + (a - b) * log23);
        if (v > max) {
          System.out.println("  new worstAll " + v + " k " + k + " at a " + a + " b " + b + 
              " choose(1, a) " + choose(1, a) + " choose(a, b) " + choose(a, b) + " (a - b) * log23 " + (a - b) * log23);
          max = v;
        }
      }
    }
    return max;
  }

  static void recurrence() {
    int n = 20;
    int s[][][][] = new int[n][n][n][n];
    s[1][0][0][0] = 1;
    s[1][0][0][1] = 1;
    s[1][0][1][0] = 1;
    s[1][1][0][1] = 1;
    s[1][1][1][0] = 1;
    s[1][1][1][1] = 1;
    for (int a = 2; a < n; a++) {
      for (int b = 1; b < n - a; b++) {
        for (int c = 0; c < a; c++) {
          s[a][b][c][1] = sumD(a + 1, s, a, b - 1, c);
          if (c > 0) {
            s[a][b][c][2] = s[a - 1][b][c - 1][1];
          }
          for (int d = 3; d <= a; d++) {
            s[a][b][c][d] = s[a - 1][b][c][d - 1];
          }
        }
      }
    }
    for (int a = 1; a < n; a++) {
      for (int b = 1; b < n - a; b++) {
        System.out.println("a " + a + "  b " + b + " sumCD " + sumCD(a + 1, s, a, b));
        for (int c = 0; c <= a; c++) {
          System.out.println("              c " + c + "  sumD " + sumD(a + 1, s, a, b, c));
          System.out.print("           ");
          for (int d = 1; d <= a; d++) {
            System.out.print(d + " : " + s[a][b][c][d] + " ");
          }
          System.out.println();
        }
      }
    }
  }

  static int sumCD(int k, int[][][][] s, int a, int b) {
    int sum = 0;
    for (int c = 0; c < k; c++) {
      sum += sumD(k, s, a, b, c);
    }
    return sum;
  }
  static int sumD(int k, int[][][][] s, int a, int b, int c) {
    int sum = 0;
    for (int i = 0; i < k; i++) {
      sum += s[a][b][c][i];
    }
    return sum; 
  }
  static void calc6() {
    double max = 0.0;
    for (int ia = 1; ia < 1000; ia += 50) {
      double a = toDouble(ia);
      for (int ib = 1; ib < ia; ib++) {
        double b = toDouble(ib);
        for (int id = 1; id < ia - ib; id++) {
          double d = toDouble(id);
          for (int ic = 1; ic < ia - ib - id; ic++) {
            //          for (int ic = 1; ic < ia - ib - id; ic++) {
            if (ib + id <= 2 * (ia - ic) / 3) {
              continue;
            }
            double c = toDouble(ic);

            double p = Math.pow(2, p8(a, b, c, d, false));
            if (p > max) {
              max = p;       
              System.out.println("new max " + max + " at a " + a + " b " + b + " c " + c + " d " + d);
              p8(a, b, c, d, true);
              //            }
            }
          }

        }
      }
    }
  }

  static double p8(double a, double b, double c, double d, boolean verbose) {

    if (verbose) {
      System.out.println("            choose(1, a) " + choose(1, a) + 
          " choose(a, b) "  + choose(a, b) + 
          " a - b - d " + (a - b - d) + " choose(a - b - d, c)  " + choose(a - b - d, c)  + 
          " a - b - d - c " + (a - b - d - c) + " * log_2 3 " + (a - b - d - c) * log23);

      //          + " choose(a - b, c) " + choose(a - b, c));
      //          " choose(a, b) "  + choose(a, b) + " choose(a - 2b, c) " + choose(a - 2 * b, c) + 
      //          " (a - 2b - c) * log_2 3 " + b * Math.log(3) / Math.log(2));

    }
    //        return choose(1, b) + Math.min(b, 1.1 * c) * Math.log(3) / Math.log(2);
    return Math.min(choose(1, a), choose(a, b)) 
        //        + choose(a - b - d, c) + b + d + c + (a - b - d - c) * log23;
        + choose(a - b - d, c) + a;
  }

  static void calc5() {
    double max = 0;
    for (int ia = 1; ia < 1000; ia += 50) {
      double a = toDouble(ia);
      for (int ib = 1; ib < ia; ib++) {
        double b = toDouble(ib);
        for (int id = 1; id <= ia - ib; id++) {
          double d = toDouble(id);
          double p = Math.pow(2, p7(a, b, d, false));
          if (p > max) {
            max = p;       
            System.out.println("new max " + max + 
                " at a " + a  + ", b " + b + ", d " + d);
            p7(a, b, d, true);
            //            }
          }

        }
      }
    }
  }


  static double p7(double a, double b, double d, boolean verbose) {
    if (verbose) {
      System.out.println("            choose(1, a) " + choose(1, a) +
          " choose(a, b) " + choose(a, b) + " choose(a - b, d) " + choose(a - b, d));
    }
    return Math.min(choose(1, a), choose (a, b)) + choose(a - b, d) + a - d;
  }

  static double p6(double a, double b, double c, double k, boolean verbose) {
    assert b <= k;
    assert a - c > k;
    assert a - c <= 3 * k / 2;
    double toIntersect = a - c - k;
    assert toIntersect < k / 2;
    if (verbose) {
      System.out.println("            choose(1, a) " + choose(1, a) +
          " choose(a, b) " + choose(a, b) + " choose(a, d) " + choose(a, c) + 
          //          " toIntersect " + toIntersect + 
          //          " choose(a - b - c, toIntersect) " + choose(a - b - c, toIntersect) +
          //      " cover(k, k - toIntersect) " + cover(k, k - toIntersect));
          "");
    }

    //    return Math.min(choose(1, a), choose (a, b)) + choose(a - b - c, toIntersect) + cover(k, k - toIntersect) + c;
    return Math.min(choose(1, a), choose (a, b)) + choose(a, c) + a - c  + c;
  }

  static double cover(double k, double k1) {
    assert 2 * k1 >= k; 
    double minIntersect = 2 * k1 - k;
    return choose(k, minIntersect) + k - minIntersect;
  }

  static void calc4() {
    double max = 0;
    for (int a = 1; a < 1000; a+= 10) {
      for (int k = 1; k < a; k+= 10) {
        for (int s = k + 1; s <= Math.min(a,  k * 3 / 2); s+= 10) {
          for (int d1 = 1; d1 < s - k; d1++) {
            for (int d2 = 1; d2 < s - k - d1; d2++) {

              double p = Math.pow(2, p5(toDouble(a), toDouble(k), toDouble(s), toDouble(d1), toDouble(d2)));
              if (p > max) {
                max = p;       
                System.out.println("new max " + max + 
                    " at a " + toDouble(a)  + ", k " + toDouble(k) + ", s " + 
                    toDouble(s) + ", d1 " + toDouble(d1) + " d2 " + toDouble(d2));
                System.out.println("           c(1, a) " + c(1, toDouble(a)) + 
                    " c(a, d1) " + c(toDouble(a), toDouble(d1)) + " c((a - d1), d2) " + c((toDouble(a) - toDouble(d1)), toDouble(d2))); 
              }
            }
          }
        }
      }
    }
  }

  static double p5(double a, double k, double s, double d1, double d2) {
    return c(1, a) +  c(a, d1) + c(a - d1, d2) + Math.min(k * 3 / 2, (a - d1 - d2)) * Math.log(3)/ Math.log(2);  
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

  static void calc1() {
    for (int i = 1; i < 10; i++) {
      double x = ((double) i) / 10.0; 
      System.out.println(x + " : " + h(x));
    }
  }

  static void calc3() {
    double max = 0;
    for (int k = 1; k < 1000; k++) {
      for (int i = 1; i < k; i++) {
        for (int j = 1; j < 1000 - i; j++) {
          for (int h = 1; h < j; h++) {

            double x = ((double) k) / 1000.0; 
            double y = ((double) i) / 1000.0; 
            double z = ((double) j) / 1000.0;
            double w = ((double) h) / 1000.0;
            if (z - w > x * 1.5) {
              continue;
            }
            double p = p4(x, y, z, w);
            if (p > max) {
              max = p;       
              System.out.println("new max " + max + 
                  " at x " + x  + ", y " + y + ", z " + z + ", w " + w);
            }
          }
        }
      }
    }
  }
  static void calc2() {
    double max = 0;
    for (int k = 1; k < 1000; k++) {
      for (int i = 1; i < 1000; i++) {
        for (int j = 1; j < k; j++) {

          double x = ((double) k) / 1000.0; 
          double y = ((double) i) / 1000.0; 
          double z = ((double) j) / 1000.0;
          double p = p3(x, y, z);
          if (p > max) {
            max = p;       
            System.out.println("new max " + max + " at x " + x  + ", y " + y + ", z " + z);
          }
        }
      }
    }
  }

  static double p4(double x, double y, double z, double w) {
    assert y <= x;
    assert w <= z;
    return Math.pow(2.0, 
        Math.min(h(y / (y + z)) * (y + z), h(y + z)) +
        h(w/z) * z + y + z);
  }

  static double p3(double z, double x, double y) {
    assert x <= z;
    return Math.pow(2.0, Math.min(h(y), (1 - y) * h(x)) + x + 
        (1 - x - y)* h((1.5 * z - x) / 1 - x - y) + 1 - y - z * 1.5);
  }

  static double p2(double x, double y) {

    return Math.pow(2.0, Math.min(h(y), (1 - y) * h(x)) + x + (Math.log(3) / Math.log(2)) * (1 - x - y));

  }
  static double p(double x, double y) {
    if (x < y) {
      return Math.pow(2.0, h(x) + x + (Math.log(3) / Math.log(2)) * (1 - x - y));
    }
    else {
      return Math.pow(2.0, h(y) + x + (Math.log(3) / Math.log(2)) * (1 - x - y));
    }

  }
  static double h(double x) {
    return -x * log2(x) - (1 - x) * log2(1 - x);
  }

  static double log2(double x) {
    return Math.log(x) / Math.log(2.0);
  }
}
