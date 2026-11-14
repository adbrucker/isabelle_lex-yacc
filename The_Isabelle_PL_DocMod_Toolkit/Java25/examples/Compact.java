import java.util.*;

String greeting = "Hello";

List<String> names() {
    return List.of("a", "b");
}

void main() {
    for (var n : names()) {
        System.out.println(greeting + " " + n);
    }
}
