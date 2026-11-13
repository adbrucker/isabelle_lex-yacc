package demo;

import java.util.List;

/** The smallest program: a class with a static method and a main method. */
public class Hello {
    static final String GREETING = "Hello, World";

    static int twice(int n) {
        return 2 * n;
    }

    public static void main(String[] args) {
        List<String> words = List.of(GREETING.split(", "));
        for (String w : words) {
            System.out.println(w + " " + twice(21));
        }
    }
}
