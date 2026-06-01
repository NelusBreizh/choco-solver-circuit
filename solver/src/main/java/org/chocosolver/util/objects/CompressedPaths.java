package org.chocosolver.util.objects;

import org.chocosolver.memory.IEnvironment;

/**
 * Provides a compressed representation of a directed graph where all directed paths are compressed into single nodes.
 * Given an extremity e of a compressed path, head[e] and tail[e] respectively indicate the start and end vertices of that path.
 * The head and tail information are valid only for extremities, this is sufficient for our usage.
 *
 * This dynamic structure runs in O(1) per update and query.
 *
 * @author Sulian Le Bozec-Chiffoleau
 */

public class CompressedPaths {
    private int size;
    private final int[] head;
    private final int[] tail;
    private int numberPaths;

    public CompressedPaths(int size) {
        this.size = size;
        this.head = new int[size];
        this.tail = new int[size];
        for (int i = 0; i < size; i++) {
            head[i] = i;
            tail[i] = i;
        }
        this.numberPaths = size;
    }

    public int getSize() {return size;}

    public int getNumberPaths() {return numberPaths;}

    public int getHead(int i) {return head[i];}

    public int getTail(int i) {return tail[i];}

    public boolean isHead(int i) {return head[i] == i;}

    public boolean isTail(int i) {return tail[i] == i;}


    /**
     * Merge two paths from extremities i and j:
     *
     * head[i] --> x --> x --> i  and j --> x --> tail[j] are merged into head[i] --> x --> x --> i --> j --> x --> tail[j].
     *
     * @Warning This method can be called only if (i,j) is not already part of a compressed path.
     */
    public void mergePaths(int i, int j, IEnvironment env) {
        assert isTail(i) && isHead(j) && getTail(j) != i && getHead(i) != j;
        if (numberPaths > 1) {
            int head_i = head[i];
            int tail_j = tail[j];
            // Update information for the new extremities
            tail[head_i] = tail_j;
            head[tail_j] = head_i;
            // Required for the isHead and isTail queries
            tail[i] = tail_j;
            head[j] = head_i;
            numberPaths--;

            // Here we store the operations to call during backtrack
            env.save(() -> {
                tail[head_i] = i;
                head[tail_j] = j;
                tail[i] = i;
                head[j] = j;
                numberPaths++;
            });
        }
    }
}

