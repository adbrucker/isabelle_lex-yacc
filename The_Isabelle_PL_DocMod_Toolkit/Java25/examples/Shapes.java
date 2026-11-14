package demo;

/** Sealed hierarchy, records and pattern matching. */
public class Shapes {
    sealed interface Shape permits Circle, Rect, Group {}

    record Circle(double r) implements Shape {
        Circle {
            if (r < 0) {
                throw new IllegalArgumentException("negative radius");
            }
        }
    }

    record Rect(double w, double h) implements Shape {}

    record Group(Shape first, Shape second) implements Shape {}

    static double area(Shape s) {
        return switch (s) {
            case Circle c -> Math.PI * c.r() * c.r();
            case Rect(double w, double h) -> w * h;
            case Group(Circle(var r), Shape other) when r > 1.0 -> area(other) + 1;
            case Group(var a, var b) -> area(a) + area(b);
        };
    }

    static String describe(Object o) {
        if (!(o instanceof Shape sh)) {
            return "not a shape";
        }
        return switch (sh) {
            case Circle _ -> "circle";
            case Rect r when r.w() == r.h() -> "square";
            case Rect _ -> "rectangle";
            case Group _ -> "group";
        };
    }
}
