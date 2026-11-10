/* A second unit, using what Lists.scala declared: */
package examples

import examples.Shapes.*

/** A class with a companion, a trait with a self type, and string interpolation. */
trait Named { self: Shape =>
  def name: String
}

case class Item(name: String, shape: Shape) {
  def describe: String = s"${name}: area ${shape.area}"
}

object Item {
  def apply(name: String): Item = new Item(name, Shape.Unit)

  def main(args: Array[String]): Unit = {
    val items = args.toList.map(Item(_))
    items.foreach { i =>
      println(i.describe)
    }
    val sizes = for {
      i <- items
      n = i.name.length
      if n > 2
    } yield n
    println(sizes.mkString(", "))
  }
}
