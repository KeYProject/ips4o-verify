package de.wiesler;

public final class Sorter {
    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Constants.ACTUAL_BASE_CASE_SIZE < end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures \result.isValidForLen(end - begin);
      @ ensures Functions.isSortedSlice(values, begin, begin + \result.num_samples);
      @ ensures \invariant_for(storage);
      @ ensures \fresh(\result);
      @
      @ // Calls sort directly => +0
      @ measured_by end - begin, 0;
      @
      @ assignable storage.allArrays;
      @ assignable values[begin..end - 1];
      @*/
    private static SampleParameters sample(int[] values, int begin, int end, Storage storage) {
        SampleParameters parameters = new SampleParameters(end - begin);
        /*@ assert sample0: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values))) \by {
                oss;
                assert "seqDef{int j;}(begin, end, any::select(heap, values, arr(j))) = seqDef{int j;}(begin, end, any::select(heapAfter_SampleParameters, values, arr(j)))" \by {
                    auto;
                }
                auto;
            }
          @*/

        Functions.select_n(values, begin, end, parameters.num_samples);
        /*@ assert sample1: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values))) \by {
                auto;
            };
          @*/

        //@ ghost \seq before_sort = \dl_seq_def_workaround(begin, end, values);
        sort(values, begin, begin + parameters.num_samples, storage);
        /*@ assert sample2: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), before_sort) \by {
                oss;
                assert "wellFormed(heapAfter_sort)" \by { auto; }                   // this is missing in the original proof by JW, but somehow needed here (automode does not find it)

                // TODO: not very robust: "self" is frequently renamed (e.g. to self_25)
                let @numSamplesFinal="int::final(self, de.wiesler.SampleParameters::$num_samples)";

                assert "seqPerm(seqDef{int j;}(add(begin, @numSamplesFinal), end, int::select(heapAfter_sort, values, arr(j))),
                                seqDef{int j;}(add(begin, @numSamplesFinal), end, any::select(heapAfter_select_n, values, arr(j))))" \by {
                    assert "seqDef{int j;}(begin + @numSamplesFinal, end, any::select(heapAfter_select_n, values, arr(j)))
                          = seqDef{int j;}(begin + @numSamplesFinal, end, values[j]@heapAfter_sort)" \by {
                        auto;
                    }
                    auto;
                }

                //rule seqPermConcatFW on="seqPerm(seqDef{int j;}(begin, add(int::_, int::_)), seqDef{int j;}(begin, add(int::_, int::_)))";            // not needed
                rule seqDef_split on="seqDef{int j;}(begin, end, any::select(heapAfter_sort, values, arr(j)))" inst_idx="begin+@numSamplesFinal";
                rule seqDef_split on="seqDef{int j;}(begin, end, any::select(heapAfter_select_n, values, arr(j)))" inst_idx="begin+@numSamplesFinal" occ=2;
                auto;
            }
          @*/

        return parameters;
    }

    /*@ public model_behaviour
      @ requires true;
      @
      @ static model boolean isBucketPartitioned(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return // for all bucket elements
      @         (\forall
      @             int i;
      @             begin + bucket_begin <= i < begin + bucket_end;
      @             // all subsequent elements are bigger
      @             (\forall int j; begin + bucket_end <= j < end; values[i] < values[j])
      @         );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[0..num_buckets + 1];
      @
      @ static model boolean allBucketsPartitioned(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return (\forall int b; 0 <= b < num_buckets; Sorter.isBucketPartitioned(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires 0 <= begin <= end <= values.length;
      @ requires nonEmptyBucketsLemma(classifier, values, begin, end, bucket_starts);
      @ requires classifier.classOfTrans();
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean allBucketsPartitionedLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return allBucketsPartitioned(values, begin, end, bucket_starts, classifier.num_buckets);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[0..num_buckets + 1];
      @
      @ static model boolean allBucketsInRangeSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return (\forall int b; lower <= b < upper; Functions.isSortedSlice(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ accessible values[begin..end - 1];
      @
      @ static model boolean isEqualityBucket(int[] values, int begin, int end) {
      @     return
      @         (\forall int i; begin <= i < end - 1; values[i] == values[i + 1]);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower && lower <= upper && upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @
      @ // accessible values[begin..end - 1], bucket_starts[lower..upper];
      @
      @ static model boolean equalityBucketsInRange(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return
      @         (\forall int b;
      @             lower <= b < upper && b % 2 == 1;
      @             Sorter.isEqualityBucket(values, begin + bucket_starts[b], begin + bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean equalityBucketsLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return classifier.equal_buckets ==>
      @         Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, classifier.num_buckets, 1, classifier.num_buckets - 1);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires true;
      @ static model boolean smallBucketIsSorted(int[] values, int begin, int end, int bucket_begin, int bucket_end) {
      @     return true;
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires 0 <= lower <= upper <= num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && end - begin == bucket_starts[num_buckets];
      @ // accessible values[begin..end - 1], bucket_starts[lower..upper];
      @
      @ static model boolean smallBucketsInRangeSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets, int lower, int upper) {
      @     return (\forall int b; lower <= b < upper; Sorter.smallBucketIsSorted(values, begin, end, bucket_starts[b], bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && len == bucket_starts[num_buckets];
      @
      @ accessible bucket_starts[0..num_buckets];
      @
      @ static model boolean notAllValuesInOneBucket(int[] bucket_starts, int num_buckets, int len) {
      @     return (\forall int b; 0 <= b < num_buckets; bucket_starts[b + 1] - bucket_starts[b] < len);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == end - begin;
      @
      @ // Buckets are partitioned
      @ requires Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @
      @ // Buckets are sorted
      @ requires Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, num_buckets);
      @
      @ requires bucketIndexFromOffset(bucket_starts, num_buckets, end - begin);
      @
      @ ensures \result;
      @
      @ static model boolean sortednessFromPartitionSorted(int[] values, int begin, int end, int[] bucket_starts, int num_buckets) {
      @     return Functions.isSortedSlice(values, begin, end);
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets);
      @ requires bucket_starts[num_buckets] == len;
      @
      @ ensures \result;
      @ // (   nv >= 0
      @ //  -> nv <= num_buckets & i_0 < bucket_starts[nv]
      @ //  -> \exists int b; (0 <= b & b < nv & bucket_starts[b] <= i_0 & i_0 < bucket_starts[b + 1]))
      @
      @ static model boolean bucketIndexFromOffset(int[] bucket_starts, int num_buckets, int len) {
      @     return (\forall int i; 0 <= i < len; (\exists int b; 0 <= b < num_buckets; bucket_starts[b] <= i < bucket_starts[b + 1]));
      @ }
      @*/

    /*@ public model_behaviour
      @ requires \invariant_for(classifier);
      @ requires Functions.isValidBucketStarts(bucket_starts, classifier.num_buckets) && end - begin == bucket_starts[classifier.num_buckets];
      @ requires bucketIndexFromOffset(bucket_starts, classifier.num_buckets, end - begin);
      @ requires Partition.allBucketsClassified(values, begin, end, classifier, bucket_starts);
      @
      @ ensures \result;
      @
      @ static model boolean nonEmptyBucketsLemma(Classifier classifier, int[] values, int begin, int end, int[] bucket_starts) {
      @     return (\forall int i; begin <= i < end;
      @         bucket_starts[classifier.classOf(values[i])] <= i - begin < bucket_starts[classifier.classOf(values[i]) + 1]
      @     );
      @ }
      @*/

    /*@ public model_behaviour
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && len == bucket_starts[num_buckets];
      @ requires (\forall int b; 0 <= b < num_buckets;
      @     (\exists int c; 0 <= c < num_buckets && b != c; bucket_starts[c] < bucket_starts[c + 1])
      @ );
      @
      @ ensures \result;
      @
      @ static model boolean notAllValuesInOneBucketLemma(int[] bucket_starts, int num_buckets, int len) {
      @     return notAllValuesInOneBucket(bucket_starts, num_buckets, len);
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires bucket_starts.length == Constants.MAX_BUCKETS + 1;
      @ requires (\forall int b; 0 <= b < bucket_starts.length; bucket_starts[b] == 0);
      @ requires end - begin > Constants.ACTUAL_BASE_CASE_SIZE;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @
      @ requires \disjoint(values[*], bucket_starts[*], storage.allArrays);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures \result != null ==>
      @     \result.num_buckets % 2 == 0 &&
      @     Functions.isValidBucketStarts(bucket_starts, \result.num_buckets) &&
      @     bucket_starts[\result.num_buckets] == end - begin &&
      @     // Buckets are partitioned
      @     Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, \result.num_buckets) &&
      @     // Small buckets are sorted
      @     Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, \result.num_buckets, 0, \result.num_buckets) &&
      @     // Equality buckets at odd indices except the last bucket
      @     (\result.equal_buckets ==> Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, \result.num_buckets, 1, \result.num_buckets - 1)) &&
      @     Sorter.notAllValuesInOneBucket(bucket_starts, \result.num_buckets, end - begin);
      @ ensures \invariant_for(storage);
      @
      @ // Calls sample which has +0 => +1
      @ measured_by end - begin, 1;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @ assignable bucket_starts[*];
      @*/
    private static /*@ nullable */ PartitionResult partition(
            int[] values,
            int begin,
            int end,
            int[] bucket_starts,
            Storage storage
    ) {
        /*@ assert \disjoint(
          @   values[*],
          @   bucket_starts[*],
          @   storage.tree[*],
          @   storage.splitters[*],
          @   storage.bucket_pointers[*],
          @   storage.buffers_buffer[*],
          @   storage.buffers_indices[*],
          @   storage.swap_1[*],
          @   storage.swap_2[*],
          @   storage.overflow[*]
          @ );
          @*/

        //@ ghost \seq oldValues = \dl_seq_def_workaround(begin, end, values);

        final SampleParameters sample = sample(values, begin, end, storage);
        final int num_samples = sample.num_samples;
        final int num_buckets = sample.num_buckets;
        final int step = sample.step;
        final int[] splitters = storage.splitters;

        //@ ghost \seq before_copy_unique = \dl_seq_def_workaround(begin, end, values);

        // Select num_buckets - 1 splitters
        final int num_splitters = Functions.copy_unique(values, begin, begin + num_samples, num_buckets - 1, step, splitters);

        //@ ghost \seq before_from_sorted_samples = \dl_seq_def_workaround(begin, end, values);
        /*@ assert before_from_sorted_samples == before_copy_unique;
          @*/
        /*@ assert \dl_seqPerm(before_from_sorted_samples, oldValues);
          @*/

        if (num_splitters <= 1) {
            return null;
        }

        // >= 2 unique splitters, therefore >= 3 buckets and >= 2 nonempty buckets
        final Classifier classifier = Classifier.from_sorted_samples(splitters, storage.tree, num_splitters, num_buckets);

        // Create this first, classifier is immutable and this removes heap mutations after partition
        final PartitionResult r = new PartitionResult(classifier.num_buckets(), classifier.equal_buckets());

        //@ ghost \seq valuesBeforePartition = \dl_seq_def_workaround(begin, end, values);
        //@ assert valuesBeforePartition == before_from_sorted_samples;
        //@ assert \invariant_for(classifier);

        //@ assert \dl_seqPerm(valuesBeforePartition, oldValues);
        //@ assert (\exists int i; begin <= i < end; (\exists int j; begin <= j < end; classifier.classOf(values[i]) != classifier.classOf(values[j])));
        Partition.partition(values, begin, end, bucket_starts, classifier, storage);

        //@ ghost \seq valuesAfterPartition = \dl_seq_def_workaround(begin, end, values);
        //@ assert bucketIndexFromOffset(bucket_starts, classifier.num_buckets, end - begin);
        /*@ assert (\exists int i; 0 <= i < valuesAfterPartition.length;
          @     (\exists int j; 0 <= j < valuesAfterPartition.length;
          @         classifier.classOf((int) valuesAfterPartition[i]) != classifier.classOf((int) valuesAfterPartition[j]))
          @ );
          @*/

        //@ assert (\exists int i; begin <= i < end; (\exists int j; begin <= j < end; classifier.classOf(values[i]) != classifier.classOf(values[j])));
        //@ assert nonEmptyBucketsLemma(classifier, values, begin, end, bucket_starts);
        //@ assert equalityBucketsLemma(classifier, values, begin, end, bucket_starts);

        //@ assert notAllValuesInOneBucketLemma(bucket_starts, classifier.num_buckets, end - begin);
        //@ assert allBucketsPartitionedLemma(classifier, values, begin, end, bucket_starts);

        // assignable: apply eq of allArrays

        return r;
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires 0 <= bucket && bucket < num_buckets;
      @ requires Functions.isValidBucketStarts(bucket_starts, num_buckets) && bucket_starts[num_buckets] == end - begin;
      @ requires Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket);
      @
      @ // Stays partitioned
      @ requires Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @ // All subsequent buckets keep the sorting property
      @ requires Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket, num_buckets);
      @ // Equality buckets
      @ requires equal_buckets ==>
      @     (bucket % 2 == 0 || bucket == num_buckets - 1) &&
      @     // starting at the next bucket, ending before the last bucket
      @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
      @ requires Sorter.notAllValuesInOneBucket(bucket_starts, num_buckets, end - begin);
      @ requires \disjoint(storage.allArrays, values[*], bucket_starts[*]);
      @ requires \invariant_for(storage);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @
      @ // Previous stay sorted, current is now sorted
      @ ensures Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket + 1);
      @ // Stays partitioned
      @ ensures Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
      @ // All subsequent buckets keep the sorting property
      @ ensures Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets);
      @ // Equality buckets at odd indices except the last bucket
      @ ensures equal_buckets ==>
      @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
      @ ensures \invariant_for(storage);
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @
      @ measured_by end - begin, 1;
      @*/
    private static void sample_sort_recurse_on(int[] values, int begin, int end, Storage storage, int[] bucket_starts, int num_buckets, boolean equal_buckets, int bucket) {
        int inner_begin = begin + bucket_starts[bucket];
        int inner_end = begin + bucket_starts[bucket + 1];

        /*@ assert ssortRec0: Functions.bucketStartsOrdering(bucket_starts, num_buckets, bucket) \by {
                oss;
                rule Contract_axiom_for_bucketStartsOrdering_in_Functions;
                auto classAxioms=false steps=50;
            }; */

        /*@ assert ssortRec1: 0 <= bucket_starts[bucket] <= bucket_starts[bucket + 1] <= bucket_starts[num_buckets] &&
                (\forall int b; 0 <= b < num_buckets && b != bucket;
                    (b < bucket ==> 0 <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[bucket]) &&
                    (b > bucket ==> bucket_starts[bucket + 1] <= bucket_starts[b] <= bucket_starts[b + 1] <= bucket_starts[num_buckets])) \by {
                expand on="de.wiesler.Functions::bucketStartsOrdering(heap, bucket_starts, num_buckets, bucket)";
                auto;
            }; */

        /*@ normal_behaviour
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin + bucket_starts[bucket], inner_end, values), \old(\dl_seq_def_workaround(begin + bucket_starts[bucket], begin + bucket_starts[bucket + 1], values)));
          @ ensures Functions.isSortedSlice(values, begin + bucket_starts[bucket], inner_end);
          @ assignable values[inner_begin..inner_end - 1], storage.allArrays;
          @ measured_by end - begin, 1;
          @*/
        {
            if (inner_end - inner_begin > Constants.ACTUAL_BASE_CASE_SIZE) {
                sample_sort(values, inner_begin, inner_end, storage);
            } else {
                base_case_sort(values, inner_begin, inner_end);
            }
        }

        /*@ assert ssortRec2: \dl_seq_def_workaround(begin, inner_begin, values) == \old(\dl_seq_def_workaround(begin, begin + bucket_starts[bucket], values)) \by {
                oss;
                auto steps=1500;
            }; */
        /*@ assert ssortRec3: \dl_seq_def_workaround(inner_end, end, values) == \old(\dl_seq_def_workaround(begin + bucket_starts[bucket + 1], end, values)) \by {
                auto steps=1500;
            }; */
        /*@ assert ssortRec4: \dl_seqPerm(\dl_seq_def_workaround(begin, inner_begin, values), \old(\dl_seq_def_workaround(begin, begin + bucket_starts[bucket], values))) \by {
                auto steps=1500;
            }; */
        /*@ assert ssortRec5: \dl_seqPerm(\dl_seq_def_workaround(inner_end, end, values), \old(\dl_seq_def_workaround(begin + bucket_starts[bucket + 1], end, values))) \by {
                auto steps=1500;
            }; */

        // individual parts of the postcondition:
        /*@ assert ssortRec_post0: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values))) \by {
                oss;
                // TODO: seems that abbreviations (bound by let) do not work in assumes
                let @middle="begin + bucket_starts[bucket]";
                let @middleSucc="begin + bucket_starts[1 + bucket]";
                rule seqPermConcatFW on="seqPerm(seqDef{int j;}(begin + bucket_starts[1 + bucket], end, any::_), seqDef{int j;}(begin + bucket_starts[1 + bucket], end, values[j]))"
                                     assumes="seqPerm(seqDef{int j;}(begin + bucket_starts[bucket], begin + bucket_starts[1 + bucket], any::_), seqDef{int j;}(begin + bucket_starts[bucket], begin + bucket_starts[1 + bucket], values[j]))==>";
                rule seqPermConcatFW on="seqPerm(seqConcat(Seq::_, Seq::_), seqConcat(Seq::_, Seq::_))"
                                     assumes="seqPerm(seqDef{int j;}(begin, begin + bucket_starts[bucket], any::_), seqDef{int j;}(begin, begin + bucket_starts[bucket], values[j]))==>";
                rule seqDef_split on="seqDef{int j;}(begin, end, any::select(anon(Heap::_, LocSet::_, Heap::_), values, arr(j)))" inst_idx="@middle";
                rule seqDef_split on="seqDef{int j;}(begin, end, any::select(heap, values, arr(j)))" inst_idx="@middle";

                assert "begin <= begin + bucket_starts[bucket] & begin + bucket_starts[bucket] < end" \by {
                    tryclose branch steps=1000;
                }

                rule replace_known_left on="begin <= begin + bucket_starts[bucket] & begin + bucket_starts[bucket] < end" occ=1;
                rule replace_known_left on="begin <= begin + bucket_starts[bucket] & begin + bucket_starts[bucket] < end" occ=1;
                oss;
                rule seqDef_split on="seqDef{int uSub1;}(@middle, end, any::select(heap, values, arr(uSub1)))" inst_idx="@middleSucc";
                rule seqDef_split on="seqDef{int uSub1;}(@middle, end, any::select(anon(Heap::_, LocSet::_, Heap::_), values, arr(uSub1)))" inst_idx="@middleSucc";

                // TODO: same problem as always: does not work
                //auto steps=1000 dependencies=false classAxioms=false modelSearch=false expandQueries=false;
                //leave;

                // workaround: this also affects all branches visited afterwards!
                set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                tryclose branch steps=1000;
            }; */

        /*@ assert ssortRec_post1: Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket + 1) \by {
                oss;
                macro "simp-int";
                expand on="de.wiesler.Sorter::allBucketsInRangeSorted(anon(Heap::_, LocSet::_, Heap::_), values, begin, end, bucket_starts, num_buckets, 0, bucket + 1)";
                oss;
                macro "simp-int";
                witness "\forall int b; (0 <= b & b <= bucket -> de.wiesler.Functions::isSortedSlice(Heap::_, int[]::_, int::_, int::_) = TRUE)" as="b_0";

                cut "b_0 != bucket";
                branches "push";
                branches "select" branch="show";
                    set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_DELAYED";
                    set key="DEP_OPTIONS_KEY" value="DEP_ON";
                    set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                    set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                    tryclose branch steps=200;
                branches "select" branch="use";
                branches "pop";

                //assert "b_0 != bucket" \by {
                    //auto steps=200 dependencies=false classAxioms=false modelSearch=false expandQueries=false;

                //    // workaround: this also affects all branches visited afterwards!
                //    set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_DELAYED";
                //    set key="DEP_OPTIONS_KEY" value="DEP_ON";
                //    set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                //    set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                //    tryclose branch steps=200;
                //}

                expand on="de.wiesler.Sorter::allBucketsInRangeSorted(Heap::_, values, begin, end, bucket_starts, num_buckets, 0, bucket)";

                // TODO: instantiate command does not support holes/ellipses at the moment
                rule allLeftHide inst_formula="\forall int b; (b < num_buckets & b >= 0 & b != bucket -> __)" inst_t="b_0";

                // TODO: in the GUI this works with the setting classAxioms:Delayed, which can not be selected in the script currently
                //auto steps=7000 dependencies=true classAxioms=true modelSearch=false expandQueries=false;
                //leave;

                // workaround: this also affects all branches visited afterwards!
                set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_DELAYED";
                set key="DEP_OPTIONS_KEY" value="DEP_ON";
                set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                tryclose branch steps=7000;

                // TODO: for some strange reason, this branch does not close directly, only when the script is applied manually in GUI ...
            }; */
        /*@ assert ssortRec_post2: Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets) \by {
                oss;
                macro "simp-int";
                expand on="de.wiesler.Sorter::allBucketsPartitioned(anon(Heap::_, LocSet::_, Heap::_), values, begin, end, bucket_starts, num_buckets)";
                oss;
                witness "\forall int b; (0 <= b & b < num_buckets -> __)" as="b_0";
                expand on="de.wiesler.Sorter::allBucketsPartitioned(heap, values, begin, end, bucket_starts, num_buckets)";
                oss;
                rule allLeftHide on="\forall int b; (b < num_buckets & b >= 0 & b != bucket -> __)" inst_t="b_0";
                expand on="de.wiesler.Sorter::isBucketPartitioned(heap, values, begin, end, int::_, int::_)";
                expand on="de.wiesler.Sorter::isBucketPartitioned(Heap::_, values, begin, end, int::_, int::_)";

                cut "0 <= b_0 & b_0 < num_buckets";
                branches "push";
                branches "select" branch="show";
                    tryclose branch steps=1000;
                branches "select" branch="use";
                branches "pop";

                macro "nosplit-prop";
                macro "simp-int";
                oss;

                rule allRight;
                macro "nosplit-prop";
                rule allRight;
                rule allLeftHide on="\forall int b; __" inst_t="b_0";

                cut "b_0 = bucket";
                branches "push";
                branches "select" branch="show";

                    cut "int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap<<anonHeapFunction>>), values, arr(i_0)) = int::select(heap, values, arr(i_0))";
                    branches "push";
                    branches "select" branch="show";
                        set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                        set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                        set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                        set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                        tryclose branch steps=2000;
                    branches "select" branch="use";
                    branches "pop";

                    rule impLeft occ=1;
                        tryclose branch steps=200;

                    cut "b_0 > bucket";
                    branches "push";
                    branches "select" branch="use";        // branches swapped!!!

                        cut "int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap), values, arr(j_0)) = int::select(heap, values, arr(j_0))";
                        branches "push";
                        branches "select" branch="show";
                            macro "simp-heap";
                            set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                            set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                            set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                            set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                            tryclose branch steps=500;
                        branches "select" branch="use";
                        branches "pop";


                        rule allLeftHide inst_t="i_0";
                        rule impLeft on="__ -> (\forall int j; __)";
                            tryclose branch steps=1000;
                        rule allLeftHide inst_t="j_0";
                        tryclose branch steps=1000;

                    branches "select" branch="show";        // branches swapped!!!
                    branches "pop";

                    rule applyEq on="int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap<<anonHeapFunction>>), values, arr(i_0))" occ=1;

                    rule allLeft inst_t="i_0";
                    rule impLeft on="__ -> (\forall int j; __)";
                            tryclose branch steps=1000;

                    rule allLeftHide on="(\forall int j; __)" inst_t="j_0" occ=0;
                    rule impLeft occ=0;
                            tryclose branch steps=1000;

                    cut "begin + bucket_starts[bucket] <= j_0 & j_0 < begin + bucket_starts[bucket + 1]";
                    branches "push";
                    branches "select" branch="show";
                        set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                        set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                        set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                        set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                        tryclose branch steps=10000;
                    branches "select" branch="use";
                    branches "pop";

                    leave;
//            // TODO: Showstopper! parameters that are variables do not work. I was not able to fix it ... When seqPermForall is applied manually, the rest of the script closes the branch.
//            rule seqPermForall inst_phi="lt(int::select(heap, values, arr(i_0)), (int)x)" inst_x=x inst_iv=iv assumes="seqPerm(seqDef{int j;}(begin + bucket_starts[bucket], int::_, any::_), Seq::_)==>";

//                     rule equiv_left;
//                         rule allLeftHide inst_t="j_0 - (begin + bucket_starts[bucket])" occ=0;
//                         tryclose branch steps=2000;
//
//                     witness "\forall int iv; (__ -> lt(int::select(heap, values, arr(i_0)), (int)(any::seqGet(seqDef{int j;}(add(begin, int::select(heap, bucket_starts, arr(bucket))), add(begin, int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))), int::select(heap, values, arr(j))), iv))))" as="iv_0";
//
//
//                     rule allLeftHide inst_t="i_0";
//                     rule impLeft on="__ -> (\forall int j; __)";
//                         tryclose branch steps=600;
//
//                     rule allLeftHide inst_t="iv_0 + begin + bucket_starts[bucket]";
//
//                     tryclose branch steps=2000;

                branches "select" branch="use";
                branches "pop";

                // TODO: works from here!
                // TODO: seems that abbreviations do not work in cuts ...
                // let @vjAtLargerHeap="int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap), values, arr(j_0))";

                cut "int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap), values, arr(j_0)) = int::select(heap, values, arr(j_0))";
                branches "push";
                branches "select" branch="show";
                    set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                    set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                    set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                    set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                    tryclose branch steps=400;
                branches "select" branch="use";
                branches "pop";

                rule applyEq on="int::select(anon(heap, union(LocSet::final(storage, de.wiesler.Storage::$allArrays), arrayRange(values, add(begin, int::select(heap, bucket_starts, arr(bucket))), add(add(Z(neglit(1(#))), begin), int::select(heap, bucket_starts, arr(add(Z(1(#)), bucket)))))), anonOut_heap), values, arr(j_0))" occ=1;

                leave;

           //     // TODO: Showstopper! parameters that are variables do not work. I was not able to fix it ...
           //     rule seqPermForall inst_phi="lt((int)x, int::select(heap, values, arr(j_0)))" inst_x=x inst_iv=iv assumes="seqPerm(seqDef{int j;}(begin + bucket_starts[bucket], int::_, any::_), Seq::_)==>";
           //
           //     rule equiv_left;
           //         rule allLeftHide inst_t="i_0 - (begin + bucket_starts[bucket])" occ=0;
           //         tryclose branch steps=2000;
           //
           //     rule allRight occ=1;
           //     rule impLeft occ=1;
           //         tryclose branch steps=50;
           //     rule allLeftHide inst_t="iv_0 + begin + bucket_starts[bucket]";
           //     tryclose branch steps=6000;
            }; */
        /*@ assert ssortRec_post3: Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets) \by {
                oss;
                macro "simp-int";
                expand on="de.wiesler.Sorter::smallBucketsInRangeSorted(anon(Heap::_, LocSet::_, Heap::_), values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets)";
                expand on="de.wiesler.Sorter::smallBucketIsSorted(anon(Heap::_, LocSet::_, Heap::_), values, begin, end, int::_, int::_)";
                tryclose branch steps=100;
            }; */
        /*@ assert ssortRec_post4: equal_buckets ==> Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1) \by {
                oss;
                rule impRight;
                macro "simp-int";
                expand on="de.wiesler.Sorter::equalityBucketsInRange(anon(Heap::_, LocSet::_, Heap::_), values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets + (-1))";
                oss;
                witness "\forall int b; (bucket + 1 <= b & b < num_buckets + (-1) & javaMod(b, 2) = 1 -> de.wiesler.Sorter::isEqualityBucket(Heap::_, int[]::_, int::_, int::_) = TRUE)" as="b_0";
                expand on="de.wiesler.Sorter::equalityBucketsInRange(heap, values, begin, end, bucket_starts, num_buckets, 1 + bucket, -1 + num_buckets)";
                oss;
                rule andLeft;
                rule allLeftHide on="\forall int b; (1 + bucket <= b & b < -1 + num_buckets & javaMod(b, 2) = 1 -> __)" inst_t="b_0";
                rule allLeftHide on="\forall int b; (b < num_buckets & b >= 0 & b != bucket -> __)" inst_t="b_0";

                // TODO: seems to be another case where the auto mode in the GUI seems to work (with the exact same settings). Also, applying the 4000 rules via script is considerably slower ...
                //auto steps=4000 dependencies=true classAxioms=false modelSearch=false expandQueries=false;

                // workaround: this also affects all branches visited afterwards!
                set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                set key="DEP_OPTIONS_KEY" value="DEP_ON";
                set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                tryclose branch steps=4000;

            }; */
        /*@ assert ssortRec_post5: \invariant_for(storage) \by {
                auto steps=1500 dependencies=true;
            }; */

        // assignable branch and rest:
        // auto steps=4000 or tryclose steps=4000 is sufficient (make sure to have the global steps >= 4000 before starting scriptAwareMacro!)
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin > Constants.ACTUAL_BASE_CASE_SIZE;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ ensures \invariant_for(storage);
      @
      @ // partition has +1, sample_sort_recurse +0 => +2
      @ measured_by end - begin, 2;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @*/
    private static void sample_sort(int[] values, int begin, int end, Storage storage) {
        int[] bucket_starts = Storage.createArray(Constants.MAX_BUCKETS + 1);

        //@ assert \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
        //@ assert \disjoint(\all_fields(values), \all_fields(bucket_starts), storage.allArrays);
        //@ assert \disjoint(storage.*, storage.allArrays);

        PartitionResult partition = partition(values, begin, end, bucket_starts, storage);

        if (partition == null) {
            fallback_sort(values, begin, end);
            return;
        }

        int num_buckets = partition.num_buckets;
        boolean equal_buckets = partition.equal_buckets;

        /*@ normal_behaviour
          @ // this is needed in many places and harder to deduce
          @ requires \disjoint(\all_fields(values), \all_fields(bucket_starts), storage.allArrays, storage.*);
          @
          @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
          @ ensures Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, num_buckets);
          @ ensures Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
          @
          @ assignable values[begin..end - 1];
          @ assignable storage.allArrays;
          @
          @ measured_by end - begin, 2;
          @*/
        {
            /*@ loop_invariant 0 <= bucket && bucket <= num_buckets;
              @ loop_invariant equal_buckets ==> bucket % 2 == 0;
              @ loop_invariant \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
              @
              @ loop_invariant Sorter.allBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, 0, bucket < num_buckets || !equal_buckets ? bucket : num_buckets - 1);
              @ // Stays partitioned
              @ loop_invariant Sorter.allBucketsPartitioned(values, begin, end, bucket_starts, num_buckets);
              @ // All subsequent buckets keep the small sorted property (especially the last one if equal_buckets)
              @ loop_invariant Sorter.smallBucketsInRangeSorted(values, begin, end, bucket_starts, num_buckets, bucket < num_buckets || !equal_buckets ? bucket : num_buckets - 1, num_buckets);
              @ loop_invariant equal_buckets ==>
              @     bucket % 2 == 0 && bucket != num_buckets - 1 &&
              @     // starting at the next bucket, ending before the last bucket
              @     Sorter.equalityBucketsInRange(values, begin, end, bucket_starts, num_buckets, bucket + 1, num_buckets - 1);
              @
              @ decreases num_buckets - bucket;
              @
              @ assignable values[begin..end - 1];
              @ assignable storage.allArrays;
              @*/
            for (int bucket = 0; bucket < num_buckets; bucket += 1 + Constants.toInt(equal_buckets)) {
                sample_sort_recurse_on(values, begin, end, storage, bucket_starts, num_buckets, equal_buckets, bucket);
            }

            if (equal_buckets) {
                sample_sort_recurse_on(values, begin, end, storage, bucket_starts, num_buckets, equal_buckets, num_buckets - 1);
            }
        }

        /*@ assert sortednessFromPartitionSorted(values, begin, end, bucket_starts, num_buckets);
          @*/
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures (\forall int element; true;
      @     Functions.countElement(values, begin, end, element) ==
      @         \old(Functions.countElement(values, begin, end, element))
      @ );
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void fallback_sort(int[] values, int begin, int end) {
        insertion_sort(values, begin, end);
        /*@ assert fallbackSort0: (\forall int element; true; Functions.countElement(values, begin, end, element) ==
                                          \old(Functions.countElement(values, begin, end, element))) \by {
                oss;
                rule allRight;

                // of these two, always only the first one works for some reason:
                //expand on="de.wiesler.Functions.countElement(values, begin, end, element_0)";
                //expand on="de.wiesler.Functions.countElement(values, begin, end, element_0)@heapAfter_insertion_sort";

                expand on="de.wiesler.Functions::countElement(heap, values, begin, end, element_0)";
                expand on="de.wiesler.Functions::countElement(heapAfter_insertion_sort, values, begin, end, element_0)";
                rule seqPermCountsInt;
                rule lenOfSeqDef occ=0;
                rule lenOfSeqDef;
                rule allLeftHide inst_t="element_0";

                assert "begin < end";

                rule bsum_shift_index occ=2;
                rule bsum_shift_index occ=3;

                assert "bsum{int uSub1;}(0, end - begin, \if (values[uSub1 + begin] = element_0) \then (1) \else (0))
                      = bsum{int iv;}(0, end - begin, \if (seqDef{int j;}(begin, end, values[j])[iv] = element_0) \then (1) \else (0))";

                // None of those is able close the goal for some reason. In the GUI, it works fine.
                // auto;
                // Not sure if the parameters actually affect anything ...
                //auto classAxioms=true expandQueries=true modelSearch=true dependencies=true proofSplitting=true steps=2000;

                // workaround (more detailed params not supported at the moment)
                tryclose branch steps=2000;
            };
          @*/
    }

    /*@ model_behaviour
      @   requires 0 <= idx < seq.length;
      @   ensures (\forall int x; 0 <= x < seq.length;
      @              \result[x] == (x == idx ? value : seq[x]));
      @   ensures \result.length == seq.length;
      @ static no_state model \seq seqUpd(\seq seq, int idx, int value) {
      @   return \seq_concat(\seq_concat(
      @     \seq_sub(seq, 0, idx),
      @     \seq_singleton(value)),
      @     \seq_sub(seq, idx+1, seq.length));
      @ }
      @*/

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    public static void insertion_sort(int[] values, int begin, int end) {
        if (end - begin < 2) return;
        int k = begin + 1;

        /*@ loop_invariant \dl_seqPerm(\dl_seq_def_workaround(begin, end, values),
          @                       \old(\dl_seq_def_workaround(begin, end, values)));
          @ loop_invariant begin < k <= end;
          @ loop_invariant (\forall int x; k <= x < end; values[x] == \old(values[x]));
          @ loop_invariant Functions.isSortedSlice(values, begin, k);
          @ assignable values[begin..end - 1];
          @ decreases end - k;
          @*/
        for (; k < end; ++k) {
            int value = values[k];
            int hole = k;

            /*@ assert insSort0: \dl_seqPerm(
                  seqUpd(\dl_seq_def_workaround(begin, end, values), hole - begin, value),
                  \old(\dl_seq_def_workaround(begin, end, values))) \by {

                    assert "seqDef{int j;}(begin, end, any::select(heap[anon(arrayRange(values, begin, -1 + end), anon_heap_LOOP)], values, arr(j)))
                        = de.wiesler.Sorter::seqUpd(seqDef{int j;}(begin, end,
                                          any::select(heap[anon(arrayRange(values, begin, -1 + end), anon_heap_LOOP)],
                                                      values,
                                                      arr(j))),
                           javaSubInt(k_0, begin), arr_0)" \by {
                        auto steps=7000 classAxioms=true dependency=false modelSearch=false expandQueries=false;
                    }
                    auto steps=200 add_applyEqReverse=high classAxioms=false dependency=false modelSearch=false expandQueries=false;
                } @*/

            /*@ loop_invariant hole == i + 1;
              @ loop_invariant begin-1 <= i < k;
              @ loop_invariant i == k - 1 || Functions.isSortedSlice(values, begin, k+1);
              @ loop_invariant Functions.isSortedSlice(values, begin, k);
              @ loop_invariant \dl_seqPerm(
              @    seqUpd(\dl_seq_def_workaround(begin, end, values), hole - begin, value),
              @    \old(\dl_seq_def_workaround(begin, end, values)));
              @ loop_invariant value <= values[hole];
              @ assignable values[begin..k];
              @ decreases i + 1;
             */
            for(int i = k - 1; i >= begin && value < values[i]; i--) {
                values[hole] = values[i];
                hole = i;

                // TODO: there seems to be a bug in interplay of loop scopes and script ("program variable h not known") -> make sure to use loop transformation rule here!
                /*@ assert insSort1: \dl_seqPerm(seqUpd(\dl_seq_def_workaround(begin, end, values), hole - begin, value), \old(\dl_seq_def_workaround(begin, end, values))) \by {
                        leave;
                    }
                  @*/
                /* @ assert insSort1: \dl_seqPerm(seqUpd(\dl_seq_def_workaround(begin, end, values), hole - begin, value), \old(\dl_seq_def_workaround(begin, end, values))) \by {

                    oss;
                    leave;

                    rule seqPermFromSwap assumes="seqPerm(de.wiesler.Sorter::seqUpd(Seq::_, int::_, int::_), seqDef{int j;}(begin, end, values[j]))==>";
                    // TODO: does not work: j (bound variable of seqDef) can not be resolved
                    //rule narrowSelectArrayType on="any::select(heap, values, arr(j))" assumes="wellFormed(heap)==>values=null";
                    assert "seqDef{int j;}(begin, end, values[j]) = seqDef{int j;}(begin, end, any::select(heap, values, arr(j)))";
                    rule replace_known_left on="seqDef{int j;}(begin, end, values[j]) = seqDef{int j;}(begin, end, any::select(heap, values, arr(j)))" occ=1;
                    oss;
                    rule exRightHide inst_t="i_0 + 1 - begin";
                    rule exRightHide inst_t="i_0 - begin";

                    // TODO: why does this not select the same term in the antecedent? bug?
                    expand on="de.wiesler.Sorter::seqUpd(Seq::_, int::_, int::_)" occ=0;
                    // expand on="de.wiesler.Sorter::seqUpd(Seq::_, int::_, int::_)" occ=0;
                    // expand on="de.wiesler.Sorter::seqUpd(Seq::_, int::_, int::_)" occ=0;
                    // expand on="de.wiesler.Sorter::seqUpd(Seq::_, int::_, int::_)" occ=0;
                    rule equalityToSeqGetAndSeqLen occ=1;

                    // TODO: not working
                    //auto steps=20000 classAxioms=false dependency=false modelSearch=false expandQueries=false;

                    // workaround:

                    set steps=20000;    // TODO: this also affects all branches visited afterwards!
                    set key="CLASS_AXIOM_OPTIONS_KEY" value="CLASS_AXIOM_OFF";
                    set key="DEP_OPTIONS_KEY" value="DEP_OFF";
                    set key="NON_LIN_ARITH_OPTIONS_KEY" value="NON_LIN_ARITH_DEF_OPS";
                    set key="QUERYAXIOM_OPTIONS_KEY" value="QUERYAXIOM_OFF";
                    tryclose;
                } @*/
            }

            // @ ghost \dl_seq tmp = \dl_seq_def_workaround(begin, end, values);

            values[hole] = value;

            // ???
            /* @ assert insSort2: \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values))) \by {
                    assert \dl_seq_def_workaround(begin, end, values) = seqUpd(tmp, begin * -1 + hole, values[k]);
                    auto;
                } @*/
        }

        /* @ assert insSort3: true \by {

                // the last branch still needs quite heavy automation ...
                auto steps=11000 dependency=false classAxioms=false expandQueries=false modelSearch=false;
            } @*/
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @
      @ assignable values[begin..end - 1];
      @*/
    private static void base_case_sort(int[] values, int begin, int end) {
        fallback_sort(values, begin, end);
    }

    /*@ public normal_behaviour
      @ requires 0 <= begin <= end <= values.length;
      @ requires end - begin <= Buffers.MAX_LEN;
      @ requires \invariant_for(storage);
      @ requires \disjoint(storage.allArrays, values[*]);
      @
      @ ensures \dl_seqPerm(\dl_seq_def_workaround(begin, end, values), \old(\dl_seq_def_workaround(begin, end, values)));
      @ ensures Functions.isSortedSlice(values, begin, end);
      @ ensures \invariant_for(storage);
      @
      @ // sample_sort has +2 => +3
      @ measured_by end - begin, 3;
      @
      @ assignable values[begin..end - 1];
      @ assignable storage.allArrays;
      @*/
    public static void sort(int[] values, int begin, int end, Storage storage) {
        if (end - begin <= Constants.ACTUAL_BASE_CASE_SIZE) {
            base_case_sort(values, begin, end);
        } else {
            sample_sort(values, begin, end, storage);
        }
    }

    /*@ public normal_behaviour
      @ requires values.length <= Buffers.MAX_LEN;
      @
      @ ensures \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values)));
      @ ensures Functions.isSortedSlice(values, 0, values.length);
      @
      @ assignable values[*];
      @*/
    public static void sort(int[] values) {
        Storage storage = new Storage();
        /*@ assert sort0: \disjoint(storage.allArrays, values[*]) \by {
                oss;
                rule disjointToElementOf;
                auto;
            }; @*/
        sort(values, 0, values.length, storage);
        /*@ assert sort1: \dl_seqPerm(\dl_array2seq(values), \old(\dl_array2seq(values))) \by {
                oss;
                assert "seqDef{int u;}(0, values.length, any::select(heap, values, arr(u))) = seqDef{int j;}(0, values.length, any::select(heapAfter_Storage, values, arr(j)))" \by {
                    auto;
                }
                auto;
            } @*/
        /*@ assert sort2: \dl_assignable(\old(\dl_heap()), values[*]) \by {
                oss;
                rule assignableDefinition;
                macro "simp-heap";
                auto;
            } @*/
    }
}
