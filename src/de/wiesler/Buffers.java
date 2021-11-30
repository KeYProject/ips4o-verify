package de.wiesler;

public class Buffers {
    public static final int BUFFER_SIZE = 1024 / 4;

    /*@ public normal_behaviour
      @  requires offset >= 0;
      @  ensures \result >= offset && Functions.isAlignedTo(\result, BUFFER_SIZE);
      @*/
    public static int align_to_next_block(int offset) {
        return (offset + BUFFER_SIZE - 1) & (-BUFFER_SIZE);
    }

    private final int[] buffer;
    private final int[] indices;

    /*@
      @ invariant this.buffer != null && this.indices != null;
      @ invariant this.buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @ invariant this.indices.length == Constants.MAX_BUCKETS;
      @ invariant (\forall int i; 0 <= i && i < this.indices.length; 0 <= this.indices[i] && this.indices[i] <= BUFFER_SIZE);
      @*/

    /*@ public normal_behaviour
      @   requires buffer != null && indices != null;
      @   requires buffer.length == 2 * Buffers.BUFFER_SIZE * Constants.MAX_BUCKETS;
      @   requires indices.length == Constants.MAX_BUCKETS;
      @*/
    public Buffers(int[] buffer, int[] indices) {
        this.buffer = buffer;
        this.indices = indices;

        Functions.fill(this.indices, 0);
    }

    /*@ public normal_behaviour
      @   requires 0 <= bucket && bucket < Constants.MAX_BUCKETS;
      @   requires Functions.isValidSlice(values, write, end);
      @   requires this.indices[bucket] == BUFFER_SIZE ==> (end - write >= BUFFER_SIZE);
      @
      @   // Todo value is inside the buffer
      @   // If \result => values[write..write + BUFFER_SIZE] is the current buffer content
      @   // Else values is unchanged
      @
      @   assignable this.indices[bucket];
      @   assignable this.buffer[bucket * BUFFER_SIZE..(bucket + 1) * BUFFER_SIZE];
      @   assignable values[write..(write + BUFFER_SIZE)];
      @*/
    public boolean push(int value, int bucket, int[] values, int write, int end) {
        int buffer_offset = bucket * BUFFER_SIZE;
        int index = this.indices[bucket];
        boolean written = false;
        if (index == BUFFER_SIZE) {
            assert (write + BUFFER_SIZE <= end);
            System.arraycopy(buffer, buffer_offset, values, write, BUFFER_SIZE);
            index = 0;
            written = true;
        }
        this.buffer[buffer_offset + index] = value;
        this.indices[bucket] = index + 1;
        return written;
    }

    /*@ public normal_behaviour
      @   requires 0 <= bucket && bucket < Constants.MAX_BUCKETS;
      @
      @   requires Functions.isValidSlice(values, head_start, head_start + head_len);
      @   requires Functions.isValidSlice(values, tail_start, tail_start + tail_len);
      @
      @   requires head_len + tail_len == this.indices[bucket];
      @
      @   assignable values[head_start..(head_start + head_len)];
      @   assignable values[tail_start..(tail_start + tail_len)];
      @*/
    public void distribute(int bucket, int[] values, int head_start, int head_len, int tail_start, int tail_len) {
        assert (head_len + tail_len == this.indices[bucket]);
        int offset = bucket * BUFFER_SIZE;
        System.arraycopy(this.buffer, offset, values, head_start, head_len);
        System.arraycopy(this.buffer, offset + head_len, values, tail_start, tail_len);
    }

    public int len(int bucket) {
        return this.indices[bucket];
    }
}
