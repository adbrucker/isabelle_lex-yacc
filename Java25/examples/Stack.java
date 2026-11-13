package demo;

import java.util.Iterator;
import java.util.NoSuchElementException;

/** A generic stack as a singly linked list, with an iterator. */
public class Stack<T> implements Iterable<T> {
    private static final class Node<E> {
        final E value;
        final Node<E> next;

        Node(E value, Node<E> next) {
            this.value = value;
            this.next = next;
        }
    }

    private Node<T> top;
    private int size;

    public void push(T x) {
        top = new Node<>(x, top);
        size++;
    }

    public T pop() {
        if (top == null) {
            throw new NoSuchElementException("empty stack");
        }
        T result = top.value;
        top = top.next;
        size--;
        return result;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    @Override
    public Iterator<T> iterator() {
        return new Iterator<T>() {
            private Node<T> cur = top;

            @Override
            public boolean hasNext() {
                return cur != null;
            }

            @Override
            public T next() {
                T v = cur.value;
                cur = cur.next;
                return v;
            }
        };
    }

    public static <E extends Comparable<? super E>> E max(Stack<E> s) {
        E best = null;
        for (E e : s) {
            if (best == null || e.compareTo(best) > 0) {
                best = e;
            }
        }
        return best;
    }
}
