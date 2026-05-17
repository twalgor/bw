package experiment;

public class test {

  public static void main(String[] args) {
    for (int i = 0; i < 20; i++) {
      System.out.println(i + " " + Integer.lowestOneBit(i));
    }

  }

}
