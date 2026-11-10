// A small Scala 3 program: an enum, an extension, a given, pattern matching and a for comprehension.
package examples

import scala.collection.mutable.{ListBuffer, Map => MMap}

enum Shape {
  case Circle(radius: Double)
  case Rect(width: Double, height: Double)
  case Unit
}

object Shapes {
  extension (s: Shape) {
    def area: Double = s match {
      case Shape.Circle(r) => math.Pi * r * r
      case Shape.Rect(w, h) => w * h
      case Shape.Unit => 1.0
    }
  }

  given Ordering[Shape] = Ordering.by(_.area)

  def total(shapes: List[Shape]): Double = {
    var sum = 0.0
    for (s <- shapes if s.area > 0.0) sum += s.area
    sum
  }

  def biggest(shapes: List[Shape])(using ord: Ordering[Shape]): Option[Shape] =
    shapes.sorted(using ord).lastOption
}
