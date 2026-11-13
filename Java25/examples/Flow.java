package demo;

import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/** Control flow: labels, loops, flow scoping of pattern variables, try with resources, lambdas. */
public class Flow {
    enum Op {
        ADD("+") {
            int apply(int a, int b) { return a + b; }
        },
        MUL("*") {
            int apply(int a, int b) { return a * b; }
        };

        final String sym;

        Op(String sym) { this.sym = sym; }

        abstract int apply(int a, int b);
    }

    static int search(int[][] grid, int target) {
        int found = -1;
        outer:
        for (int i = 0; i < grid.length; i++) {
            for (int j = 0; j < grid[i].length; j++) {
                if (grid[i][j] == target) {
                    found = i * 100 + j;
                    break outer;
                }
                if (grid[i][j] < 0) {
                    continue outer;
                }
            }
        }
        return found;
    }

    static int length(Object o) {
        if (!(o instanceof String s)) {
            return -1;
        }
        return s.length();
    }

    static int first(String text) throws IOException {
        try (var in = new StringReader(text); var again = in) {
            return again.read();
        } catch (IOException | RuntimeException e) {
            throw e;
        } finally {
            System.out.println("done");
        }
    }

    static <T, R> List<R> mapAll(List<T> xs, Function<? super T, ? extends R> f) {
        List<R> out = new ArrayList<>();
        xs.forEach(x -> out.add(f.apply(x)));
        return out;
    }

    static int kind(int k) {
        int r = 0;
        switch (k) {
            case 1:
                int x = k * 2;
                r += x;
                break;
            case 2:
                x = 5;
                r += x;
            default:
                r--;
        }
        return r;
    }
}
