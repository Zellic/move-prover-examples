module address::step_7 {
    use std::vector;

    fun looper(input: u64): u64 {
        input = if (input < 50) input else 50;
        while ({
            spec {
                invariant input <= 50;
            };

            (input < 50)
        }) {
            input = input + 1;
        };
        input
    }

    spec looper {
        ensures input == 50;
    }

    fun max(values: &vector<u64>): u64 {
        let max = *vector::borrow(values, 0);
        let index = 0;
        while ({
            spec {
                invariant forall i in 0..index: max >= values[i];
                invariant contains(values, max);
            };

            (index < vector::length(values))
        }) {
            let current = *vector::borrow(values, index);
            max = if (current > max) current else max;
            index = index + 1;
        };
        max
    }

    spec max {
        ensures forall i in 0..len(values): result >= values[i];
        ensures contains(values, result);
    }
}
