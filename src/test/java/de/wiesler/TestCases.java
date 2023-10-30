package de.wiesler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;
public class TestCases {

    private final static int SIZE = 100_000;
    private final static int LARGE = 2 << 22;

    @ParameterizedTest
    @ValueSource(ints = { 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20 })
    void doRandomTest(int seed) {
        Random r = new Random(seed);
        doRandomTest(r, SIZE);
    }

    // @Test // Ignore as it raises Out of Memory
    void testSortLarge() {
        Random r = new Random(42);
        doRandomTest(r, LARGE);
    }

    @Test
    void testAllZeros() {
        doTest(new int[SIZE]);
    }

    @Test
    void testAlreadySorted() {
        int[] array = new int[SIZE];

        for (int i = 0; i < array.length; i++) {
            array[i] = i;
        }

        doTest(array);
    }

    private static void doRandomTest(Random r, int k) {
        int[] array = new int[k];

        for (int i = 0; i < array.length; i++) {
            array[i] = r.nextInt();
        }

        doTest(array);
    }

    private static void doTest(int[] array) {
        Map<Integer, Integer> orgCount = count(array);
        Sorter.sort(array);
        Map<Integer, Integer> newCount = count(array);

        checkSorted(array);

        assertEquals(orgCount, newCount, "Permutation");
    }


    private static void checkSorted(int[] array) {
        for (int i = 1; i < array.length; i++) {
            assertTrue(array[i - 1] <= array[i], "Sortedness");
        }
    }

    private static Map<Integer, Integer> count(int[] array) {
        Map<Integer, Integer> result = new HashMap<>();
        for (int val : array) {
             int c = result.getOrDefault(val, 0);
             result.put(val, c + 1);
        }
        return result;
    }
}
