
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;

// The location of an uninitialized mutation. Using this to make sure that the location
// will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
function {:constructor} $Uninitialized(): $Location;

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) && p#$Mutation(parent) == p#$Mutation(child)
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/64/128
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 256;
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 18446744073709551616;
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 340282366920938463463374607431768211456;
}

// We don't need to know the size of destination, so no $ShrU8, etc.
procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}



//==================================
// Begin Translation



// Given Types for Type Parameters


// spec fun at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:12:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
}

// fun signer::address_of [baseline] at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:12:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:12:5+1
    assume {:print "$at(10,389,390)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:13:10+17
    assume {:print "$at(10,443,460)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(10,443,460)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(10,465,466)"} true;
L1:

    // return $t1 at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(10,465,466)"} true;
    $ret0 := $t1;
    return;

    // label L2 at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:14:5+1
L2:

    // abort($t2) at /home/daniel/.move/https___github_com_move-language_move_git_main/language/move-stdlib/sources/signer.move:14:5+1
    assume {:print "$at(10,465,466)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// spec fun at ./sources/coin.move:12:10+60
function {:inline} $2_coin_address_of(s: $signer): int {
    $1_signer_$address_of(s)
}

// spec fun at ./sources/coin.move:13:10+59
function {:inline} $2_coin_balance($2_coin_Account_$memory: $Memory $2_coin_Account, a: int): int {
    $balance#$2_coin_Account($ResourceValue($2_coin_Account_$memory, a))
}

// struct coin::Account at ./sources/coin.move:8:5+51
type {:datatype} $2_coin_Account;
function {:constructor} $2_coin_Account($balance: int): $2_coin_Account;
function {:inline} $Update'$2_coin_Account'_balance(s: $2_coin_Account, x: int): $2_coin_Account {
    $2_coin_Account(x)
}
function $IsValid'$2_coin_Account'(s: $2_coin_Account): bool {
    $IsValid'u64'($balance#$2_coin_Account(s))
}
function {:inline} $IsEqual'$2_coin_Account'(s1: $2_coin_Account, s2: $2_coin_Account): bool {
    s1 == s2
}
var $2_coin_Account_$memory: $Memory $2_coin_Account;

// fun coin::create_account [verification] at ./sources/coin.move:15:5+210
procedure {:timeLimit 40} $2_coin_create_account$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: bool;
    var $t6: bool;
    var $t7: int;
    var $t8: int;
    var $t9: $2_coin_Account;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $2_coin_Account_$memory#4: $Memory $2_coin_Account;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/coin.move:15:5+1
    assume {:print "$at(2,307,308)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<coin::Account>(): WellFormed($rsc) at ./sources/coin.move:15:5+1
    assume (forall $a_0: int :: {$ResourceValue($2_coin_Account_$memory, $a_0)}(var $rsc := $ResourceValue($2_coin_Account_$memory, $a_0);
    ($IsValid'$2_coin_Account'($rsc))));

    // assume Identical($t2, coin::address_of($t0)) at ./sources/coin.move:24:9+28
    assume {:print "$at(2,553,581)"} true;
    assume ($t2 == $2_coin_address_of($t0));

    // @4 := save_mem(coin::Account) at ./sources/coin.move:15:5+1
    assume {:print "$at(2,307,308)"} true;
    $2_coin_Account_$memory#4 := $2_coin_Account_$memory;

    // trace_local[s]($t0) at ./sources/coin.move:15:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t3 := signer::address_of($t0) on_abort goto L3 with $t4 at ./sources/coin.move:16:23+22
    assume {:print "$at(2,368,390)"} true;
    call $t3 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,368,390)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,0):", $t4} $t4 == $t4;
        goto L3;
    }

    // trace_local[address]($t3) at ./sources/coin.move:16:13+7
    assume {:print "$track_local(1,0,1):", $t3} $t3 == $t3;

    // $t5 := exists<coin::Account>($t3) at ./sources/coin.move:17:18+6
    assume {:print "$at(2,409,415)"} true;
    $t5 := $ResourceExists($2_coin_Account_$memory, $t3);

    // $t6 := !($t5) at ./sources/coin.move:17:17+1
    call $t6 := $Not($t5);

    // if ($t6) goto L0 else goto L1 at ./sources/coin.move:17:9+37
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at ./sources/coin.move:17:44+1
L1:

    // $t7 := 0 at ./sources/coin.move:17:44+1
    assume {:print "$at(2,435,436)"} true;
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at ./sources/coin.move:17:9+37
    assume {:print "$at(2,400,437)"} true;
    assume {:print "$track_abort(1,0):", $t7} $t7 == $t7;

    // $t4 := move($t7) at ./sources/coin.move:17:9+37
    $t4 := $t7;

    // goto L3 at ./sources/coin.move:17:9+37
    goto L3;

    // label L0 at ./sources/coin.move:18:26+2
    assume {:print "$at(2,464,466)"} true;
L0:

    // $t8 := 1 at ./sources/coin.move:19:22+1
    assume {:print "$at(2,499,500)"} true;
    $t8 := 1;
    assume $IsValid'u64'($t8);

    // $t9 := pack coin::Account($t8) at ./sources/coin.move:18:30+42
    assume {:print "$at(2,468,510)"} true;
    $t9 := $2_coin_Account($t8);

    // move_to<coin::Account>($t9, $t0) on_abort goto L3 with $t4 at ./sources/coin.move:18:9+7
    if ($ResourceExists($2_coin_Account_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $2_coin_Account_$memory := $ResourceUpdate($2_coin_Account_$memory, $addr#$signer($t0), $t9);
    }
    if ($abort_flag) {
        assume {:print "$at(2,447,454)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,0):", $t4} $t4 == $t4;
        goto L3;
    }

    // label L2 at ./sources/coin.move:21:5+1
    assume {:print "$at(2,516,517)"} true;
L2:

    // assert Not(exists[@4]<coin::Account>($t2)) at ./sources/coin.move:25:9+35
    assume {:print "$at(2,590,625)"} true;
    assert {:msg "assert_failed(2,590,625): function does not abort under this condition"}
      !$ResourceExists($2_coin_Account_$memory#4, $t2);

    // assert exists<coin::Account>($t2) at ./sources/coin.move:26:9+33
    assume {:print "$at(2,634,667)"} true;
    assert {:msg "assert_failed(2,634,667): post-condition does not hold"}
      $ResourceExists($2_coin_Account_$memory, $t2);

    // assert Eq<u64>(coin::balance($t2), 1) at ./sources/coin.move:27:9+30
    assume {:print "$at(2,676,706)"} true;
    assert {:msg "assert_failed(2,676,706): post-condition does not hold"}
      $IsEqual'u64'($2_coin_balance($2_coin_Account_$memory, $t2), 1);

    // return () at ./sources/coin.move:27:9+30
    return;

    // label L3 at ./sources/coin.move:21:5+1
    assume {:print "$at(2,516,517)"} true;
L3:

    // assert exists[@4]<coin::Account>($t2) at ./sources/coin.move:23:5+189
    assume {:print "$at(2,523,712)"} true;
    assert {:msg "assert_failed(2,523,712): abort not covered by any of the `aborts_if` clauses"}
      $ResourceExists($2_coin_Account_$memory#4, $t2);

    // abort($t4) at ./sources/coin.move:23:5+189
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun coin::deposit [baseline] at ./sources/coin.move:40:5+176
procedure {:inline 1} $2_coin_deposit(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: $Mutation ($2_coin_Account);
    var $t3: $Mutation ($2_coin_Account);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t0: int;
    var $t1: int;
    var $temp_0'$2_coin_Account': $2_coin_Account;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[target]($t0) at ./sources/coin.move:40:5+1
    assume {:print "$at(2,1016,1017)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/coin.move:40:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t3 := borrow_global<coin::Account>($t0) on_abort goto L2 with $t4 at ./sources/coin.move:41:23+17
    assume {:print "$at(2,1099,1116)"} true;
    if (!$ResourceExists($2_coin_Account_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($2_coin_Account_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1099,1116)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,1):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_local[account]($t3) at ./sources/coin.move:41:13+7
    $temp_0'$2_coin_Account' := $Dereference($t3);
    assume {:print "$track_local(1,1,2):", $temp_0'$2_coin_Account'} $temp_0'$2_coin_Account' == $temp_0'$2_coin_Account';

    // $t5 := get_field<coin::Account>.balance($t3) at ./sources/coin.move:42:27+15
    assume {:print "$at(2,1161,1176)"} true;
    $t5 := $balance#$2_coin_Account($Dereference($t3));

    // $t6 := +($t5, $t1) on_abort goto L2 with $t4 at ./sources/coin.move:42:43+1
    call $t6 := $AddU64($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1177,1178)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,1):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := borrow_field<coin::Account>.balance($t3) at ./sources/coin.move:42:9+15
    $t7 := $ChildMutation($t3, 0, $balance#$2_coin_Account($Dereference($t3)));

    // write_ref($t7, $t6) at ./sources/coin.move:42:9+42
    $t7 := $UpdateMutation($t7, $t6);

    // write_back[Reference($t3).balance (u64)]($t7) at ./sources/coin.move:42:9+42
    $t3 := $UpdateMutation($t3, $Update'$2_coin_Account'_balance($Dereference($t3), $Dereference($t7)));

    // write_back[coin::Account@]($t3) at ./sources/coin.move:42:9+42
    $2_coin_Account_$memory := $ResourceUpdate($2_coin_Account_$memory, $GlobalLocationAddress($t3),
        $Dereference($t3));

    // label L1 at ./sources/coin.move:43:5+1
    assume {:print "$at(2,1191,1192)"} true;
L1:

    // return () at ./sources/coin.move:43:5+1
    assume {:print "$at(2,1191,1192)"} true;
    return;

    // label L2 at ./sources/coin.move:43:5+1
L2:

    // abort($t4) at ./sources/coin.move:43:5+1
    assume {:print "$at(2,1191,1192)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun coin::deposit [verification] at ./sources/coin.move:40:5+176
procedure {:timeLimit 40} $2_coin_deposit$verify(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: $Mutation ($2_coin_Account);
    var $t3: $Mutation ($2_coin_Account);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t0: int;
    var $t1: int;
    var $temp_0'$2_coin_Account': $2_coin_Account;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $2_coin_Account_$memory#2: $Memory $2_coin_Account;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/coin.move:40:5+1
    assume {:print "$at(2,1016,1017)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/coin.move:40:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<coin::Account>(): WellFormed($rsc) at ./sources/coin.move:40:5+1
    assume (forall $a_0: int :: {$ResourceValue($2_coin_Account_$memory, $a_0)}(var $rsc := $ResourceValue($2_coin_Account_$memory, $a_0);
    ($IsValid'$2_coin_Account'($rsc))));

    // @2 := save_mem(coin::Account) at ./sources/coin.move:40:5+1
    $2_coin_Account_$memory#2 := $2_coin_Account_$memory;

    // trace_local[target]($t0) at ./sources/coin.move:40:5+1
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/coin.move:40:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t3 := borrow_global<coin::Account>($t0) on_abort goto L2 with $t4 at ./sources/coin.move:41:23+17
    assume {:print "$at(2,1099,1116)"} true;
    if (!$ResourceExists($2_coin_Account_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($2_coin_Account_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1099,1116)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,1):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_local[account]($t3) at ./sources/coin.move:41:13+7
    $temp_0'$2_coin_Account' := $Dereference($t3);
    assume {:print "$track_local(1,1,2):", $temp_0'$2_coin_Account'} $temp_0'$2_coin_Account' == $temp_0'$2_coin_Account';

    // $t5 := get_field<coin::Account>.balance($t3) at ./sources/coin.move:42:27+15
    assume {:print "$at(2,1161,1176)"} true;
    $t5 := $balance#$2_coin_Account($Dereference($t3));

    // $t6 := +($t5, $t1) on_abort goto L2 with $t4 at ./sources/coin.move:42:43+1
    call $t6 := $AddU64($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1177,1178)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,1):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := borrow_field<coin::Account>.balance($t3) at ./sources/coin.move:42:9+15
    $t7 := $ChildMutation($t3, 0, $balance#$2_coin_Account($Dereference($t3)));

    // write_ref($t7, $t6) at ./sources/coin.move:42:9+42
    $t7 := $UpdateMutation($t7, $t6);

    // write_back[Reference($t3).balance (u64)]($t7) at ./sources/coin.move:42:9+42
    $t3 := $UpdateMutation($t3, $Update'$2_coin_Account'_balance($Dereference($t3), $Dereference($t7)));

    // write_back[coin::Account@]($t3) at ./sources/coin.move:42:9+42
    $2_coin_Account_$memory := $ResourceUpdate($2_coin_Account_$memory, $GlobalLocationAddress($t3),
        $Dereference($t3));

    // label L1 at ./sources/coin.move:43:5+1
    assume {:print "$at(2,1191,1192)"} true;
L1:

    // assert Not(Not(exists[@2]<coin::Account>($t0))) at ./sources/coin.move:46:9+35
    assume {:print "$at(2,1221,1256)"} true;
    assert {:msg "assert_failed(2,1221,1256): function does not abort under this condition"}
      !!$ResourceExists($2_coin_Account_$memory#2, $t0);

    // assert Not(Gt(Add(coin::balance[@2]($t0), $t1), 18446744073709551615)) at ./sources/coin.move:47:9+45
    assume {:print "$at(2,1265,1310)"} true;
    assert {:msg "assert_failed(2,1265,1310): function does not abort under this condition"}
      !(($2_coin_balance($2_coin_Account_$memory#2, $t0) + $t1) > 18446744073709551615);

    // return () at ./sources/coin.move:47:9+45
    return;

    // label L2 at ./sources/coin.move:43:5+1
    assume {:print "$at(2,1191,1192)"} true;
L2:

    // assert Or(Not(exists[@2]<coin::Account>($t0)), Gt(Add(coin::balance[@2]($t0), $t1), 18446744073709551615)) at ./sources/coin.move:45:5+118
    assume {:print "$at(2,1198,1316)"} true;
    assert {:msg "assert_failed(2,1198,1316): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($2_coin_Account_$memory#2, $t0) || (($2_coin_balance($2_coin_Account_$memory#2, $t0) + $t1) > 18446744073709551615));

    // abort($t4) at ./sources/coin.move:45:5+118
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun coin::transfer [verification] at ./sources/coin.move:50:5+247
procedure {:timeLimit 40} $2_coin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    var $2_coin_Account_$memory#5: $Memory $2_coin_Account;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/coin.move:50:5+1
    assume {:print "$at(2,1322,1323)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at ./sources/coin.move:50:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/coin.move:50:5+1
    assume $IsValid'u64'($t2);

    // assume forall $rsc: ResourceDomain<coin::Account>(): WellFormed($rsc) at ./sources/coin.move:50:5+1
    assume (forall $a_0: int :: {$ResourceValue($2_coin_Account_$memory, $a_0)}(var $rsc := $ResourceValue($2_coin_Account_$memory, $a_0);
    ($IsValid'$2_coin_Account'($rsc))));

    // assume Identical($t4, coin::address_of($t0)) at ./sources/coin.move:62:9+25
    assume {:print "$at(2,1599,1624)"} true;
    assume ($t4 == $2_coin_address_of($t0));

    // @5 := save_mem(coin::Account) at ./sources/coin.move:50:5+1
    assume {:print "$at(2,1322,1323)"} true;
    $2_coin_Account_$memory#5 := $2_coin_Account_$memory;

    // trace_local[s]($t0) at ./sources/coin.move:50:5+1
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at ./sources/coin.move:50:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at ./sources/coin.move:50:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t5 := signer::address_of($t0) on_abort goto L3 with $t6 at ./sources/coin.move:55:20+22
    assume {:print "$at(2,1447,1469)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1447,1469)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,2):", $t6} $t6 == $t6;
        goto L3;
    }

    // trace_local[from]($t5) at ./sources/coin.move:55:13+4
    assume {:print "$track_local(1,2,3):", $t5} $t5 == $t5;

    // $t7 := !=($t5, $t1) at ./sources/coin.move:56:22+2
    assume {:print "$at(2,1492,1494)"} true;
    $t7 := !$IsEqual'address'($t5, $t1);

    // if ($t7) goto L0 else goto L1 at ./sources/coin.move:56:9+22
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./sources/coin.move:56:29+1
L1:

    // $t8 := 0 at ./sources/coin.move:56:29+1
    assume {:print "$at(2,1499,1500)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./sources/coin.move:56:9+22
    assume {:print "$at(2,1479,1501)"} true;
    assume {:print "$track_abort(1,2):", $t8} $t8 == $t8;

    // $t6 := move($t8) at ./sources/coin.move:56:9+22
    $t6 := $t8;

    // goto L3 at ./sources/coin.move:56:9+22
    goto L3;

    // label L0 at ./sources/coin.move:57:18+4
    assume {:print "$at(2,1520,1524)"} true;
L0:

    // coin::withdraw($t5, $t2) on_abort goto L3 with $t6 at ./sources/coin.move:57:9+22
    assume {:print "$at(2,1511,1533)"} true;
    call $2_coin_withdraw($t5, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1511,1533)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,2):", $t6} $t6 == $t6;
        goto L3;
    }

    // coin::deposit($t1, $t2) on_abort goto L3 with $t6 at ./sources/coin.move:58:9+19
    assume {:print "$at(2,1543,1562)"} true;
    call $2_coin_deposit($t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1543,1562)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,2):", $t6} $t6 == $t6;
        goto L3;
    }

    // label L2 at ./sources/coin.move:59:5+1
    assume {:print "$at(2,1568,1569)"} true;
L2:

    // assert Not(Eq<address>($t4, $t1)) at ./sources/coin.move:63:9+21
    assume {:print "$at(2,1633,1654)"} true;
    assert {:msg "assert_failed(2,1633,1654): function does not abort under this condition"}
      !$IsEqual'address'($t4, $t1);

    // assert Not(Not(exists[@5]<coin::Account>($t4))) at ./sources/coin.move:64:9+33
    assume {:print "$at(2,1663,1696)"} true;
    assert {:msg "assert_failed(2,1663,1696): function does not abort under this condition"}
      !!$ResourceExists($2_coin_Account_$memory#5, $t4);

    // assert Not(Not(exists[@5]<coin::Account>($t1))) at ./sources/coin.move:65:9+31
    assume {:print "$at(2,1705,1736)"} true;
    assert {:msg "assert_failed(2,1705,1736): function does not abort under this condition"}
      !!$ResourceExists($2_coin_Account_$memory#5, $t1);

    // assert Not(Lt(coin::balance[@5]($t4), $t2)) at ./sources/coin.move:66:9+33
    assume {:print "$at(2,1745,1778)"} true;
    assert {:msg "assert_failed(2,1745,1778): function does not abort under this condition"}
      !($2_coin_balance($2_coin_Account_$memory#5, $t4) < $t2);

    // assert Not(Gt(Add(coin::balance[@5]($t1), $t2), 18446744073709551615)) at ./sources/coin.move:67:9+41
    assume {:print "$at(2,1787,1828)"} true;
    assert {:msg "assert_failed(2,1787,1828): function does not abort under this condition"}
      !(($2_coin_balance($2_coin_Account_$memory#5, $t1) + $t2) > 18446744073709551615);

    // assert Eq<u64>(coin::balance($t4), Sub(coin::balance[@5]($t4), $t2)) at ./sources/coin.move:69:9+53
    assume {:print "$at(2,1838,1891)"} true;
    assert {:msg "assert_failed(2,1838,1891): post-condition does not hold"}
      $IsEqual'u64'($2_coin_balance($2_coin_Account_$memory, $t4), ($2_coin_balance($2_coin_Account_$memory#5, $t4) - $t2));

    // assert Eq<u64>(coin::balance($t1), Add(coin::balance[@5]($t1), $t2)) at ./sources/coin.move:70:9+49
    assume {:print "$at(2,1900,1949)"} true;
    assert {:msg "assert_failed(2,1900,1949): post-condition does not hold"}
      $IsEqual'u64'($2_coin_balance($2_coin_Account_$memory, $t1), ($2_coin_balance($2_coin_Account_$memory#5, $t1) + $t2));

    // return () at ./sources/coin.move:70:9+49
    return;

    // label L3 at ./sources/coin.move:59:5+1
    assume {:print "$at(2,1568,1569)"} true;
L3:

    // assert Or(Or(Or(Or(Eq<address>($t4, $t1), Not(exists[@5]<coin::Account>($t4))), Not(exists[@5]<coin::Account>($t1))), Lt(coin::balance[@5]($t4), $t2)), Gt(Add(coin::balance[@5]($t1), $t2), 18446744073709551615)) at ./sources/coin.move:61:5+380
    assume {:print "$at(2,1575,1955)"} true;
    assert {:msg "assert_failed(2,1575,1955): abort not covered by any of the `aborts_if` clauses"}
      (((($IsEqual'address'($t4, $t1) || !$ResourceExists($2_coin_Account_$memory#5, $t4)) || !$ResourceExists($2_coin_Account_$memory#5, $t1)) || ($2_coin_balance($2_coin_Account_$memory#5, $t4) < $t2)) || (($2_coin_balance($2_coin_Account_$memory#5, $t1) + $t2) > 18446744073709551615));

    // abort($t6) at ./sources/coin.move:61:5+380
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun coin::withdraw [baseline] at ./sources/coin.move:30:5+177
procedure {:inline 1} $2_coin_withdraw(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: $Mutation ($2_coin_Account);
    var $t3: $Mutation ($2_coin_Account);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t0: int;
    var $t1: int;
    var $temp_0'$2_coin_Account': $2_coin_Account;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[target]($t0) at ./sources/coin.move:30:5+1
    assume {:print "$at(2,718,719)"} true;
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/coin.move:30:5+1
    assume {:print "$track_local(1,3,1):", $t1} $t1 == $t1;

    // $t3 := borrow_global<coin::Account>($t0) on_abort goto L2 with $t4 at ./sources/coin.move:31:23+17
    assume {:print "$at(2,802,819)"} true;
    if (!$ResourceExists($2_coin_Account_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($2_coin_Account_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,802,819)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_local[account]($t3) at ./sources/coin.move:31:13+7
    $temp_0'$2_coin_Account' := $Dereference($t3);
    assume {:print "$track_local(1,3,2):", $temp_0'$2_coin_Account'} $temp_0'$2_coin_Account' == $temp_0'$2_coin_Account';

    // $t5 := get_field<coin::Account>.balance($t3) at ./sources/coin.move:32:27+15
    assume {:print "$at(2,864,879)"} true;
    $t5 := $balance#$2_coin_Account($Dereference($t3));

    // $t6 := -($t5, $t1) on_abort goto L2 with $t4 at ./sources/coin.move:32:43+1
    call $t6 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,880,881)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := borrow_field<coin::Account>.balance($t3) at ./sources/coin.move:32:9+15
    $t7 := $ChildMutation($t3, 0, $balance#$2_coin_Account($Dereference($t3)));

    // write_ref($t7, $t6) at ./sources/coin.move:32:9+42
    $t7 := $UpdateMutation($t7, $t6);

    // write_back[Reference($t3).balance (u64)]($t7) at ./sources/coin.move:32:9+42
    $t3 := $UpdateMutation($t3, $Update'$2_coin_Account'_balance($Dereference($t3), $Dereference($t7)));

    // write_back[coin::Account@]($t3) at ./sources/coin.move:32:9+42
    $2_coin_Account_$memory := $ResourceUpdate($2_coin_Account_$memory, $GlobalLocationAddress($t3),
        $Dereference($t3));

    // label L1 at ./sources/coin.move:33:5+1
    assume {:print "$at(2,894,895)"} true;
L1:

    // return () at ./sources/coin.move:33:5+1
    assume {:print "$at(2,894,895)"} true;
    return;

    // label L2 at ./sources/coin.move:33:5+1
L2:

    // abort($t4) at ./sources/coin.move:33:5+1
    assume {:print "$at(2,894,895)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun coin::withdraw [verification] at ./sources/coin.move:30:5+177
procedure {:timeLimit 40} $2_coin_withdraw$verify(_$t0: int, _$t1: int) returns ()
{
    // declare local variables
    var $t2: $Mutation ($2_coin_Account);
    var $t3: $Mutation ($2_coin_Account);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t0: int;
    var $t1: int;
    var $temp_0'$2_coin_Account': $2_coin_Account;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $2_coin_Account_$memory#0: $Memory $2_coin_Account;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/coin.move:30:5+1
    assume {:print "$at(2,718,719)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/coin.move:30:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<coin::Account>(): WellFormed($rsc) at ./sources/coin.move:30:5+1
    assume (forall $a_0: int :: {$ResourceValue($2_coin_Account_$memory, $a_0)}(var $rsc := $ResourceValue($2_coin_Account_$memory, $a_0);
    ($IsValid'$2_coin_Account'($rsc))));

    // @0 := save_mem(coin::Account) at ./sources/coin.move:30:5+1
    $2_coin_Account_$memory#0 := $2_coin_Account_$memory;

    // trace_local[target]($t0) at ./sources/coin.move:30:5+1
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at ./sources/coin.move:30:5+1
    assume {:print "$track_local(1,3,1):", $t1} $t1 == $t1;

    // $t3 := borrow_global<coin::Account>($t0) on_abort goto L2 with $t4 at ./sources/coin.move:31:23+17
    assume {:print "$at(2,802,819)"} true;
    if (!$ResourceExists($2_coin_Account_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t3 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($2_coin_Account_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,802,819)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_local[account]($t3) at ./sources/coin.move:31:13+7
    $temp_0'$2_coin_Account' := $Dereference($t3);
    assume {:print "$track_local(1,3,2):", $temp_0'$2_coin_Account'} $temp_0'$2_coin_Account' == $temp_0'$2_coin_Account';

    // $t5 := get_field<coin::Account>.balance($t3) at ./sources/coin.move:32:27+15
    assume {:print "$at(2,864,879)"} true;
    $t5 := $balance#$2_coin_Account($Dereference($t3));

    // $t6 := -($t5, $t1) on_abort goto L2 with $t4 at ./sources/coin.move:32:43+1
    call $t6 := $Sub($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,880,881)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,3):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := borrow_field<coin::Account>.balance($t3) at ./sources/coin.move:32:9+15
    $t7 := $ChildMutation($t3, 0, $balance#$2_coin_Account($Dereference($t3)));

    // write_ref($t7, $t6) at ./sources/coin.move:32:9+42
    $t7 := $UpdateMutation($t7, $t6);

    // write_back[Reference($t3).balance (u64)]($t7) at ./sources/coin.move:32:9+42
    $t3 := $UpdateMutation($t3, $Update'$2_coin_Account'_balance($Dereference($t3), $Dereference($t7)));

    // write_back[coin::Account@]($t3) at ./sources/coin.move:32:9+42
    $2_coin_Account_$memory := $ResourceUpdate($2_coin_Account_$memory, $GlobalLocationAddress($t3),
        $Dereference($t3));

    // label L1 at ./sources/coin.move:33:5+1
    assume {:print "$at(2,894,895)"} true;
L1:

    // assert Not(Not(exists[@0]<coin::Account>($t0))) at ./sources/coin.move:36:9+35
    assume {:print "$at(2,925,960)"} true;
    assert {:msg "assert_failed(2,925,960): function does not abort under this condition"}
      !!$ResourceExists($2_coin_Account_$memory#0, $t0);

    // assert Not(Lt(coin::balance[@0]($t0), $t1)) at ./sources/coin.move:37:9+35
    assume {:print "$at(2,969,1004)"} true;
    assert {:msg "assert_failed(2,969,1004): function does not abort under this condition"}
      !($2_coin_balance($2_coin_Account_$memory#0, $t0) < $t1);

    // return () at ./sources/coin.move:37:9+35
    return;

    // label L2 at ./sources/coin.move:33:5+1
    assume {:print "$at(2,894,895)"} true;
L2:

    // assert Or(Not(exists[@0]<coin::Account>($t0)), Lt(coin::balance[@0]($t0), $t1)) at ./sources/coin.move:35:5+109
    assume {:print "$at(2,901,1010)"} true;
    assert {:msg "assert_failed(2,901,1010): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($2_coin_Account_$memory#0, $t0) || ($2_coin_balance($2_coin_Account_$memory#0, $t0) < $t1));

    // abort($t4) at ./sources/coin.move:35:5+109
    $abort_code := $t4;
    $abort_flag := true;
    return;

}
