import KanTactics

/-!
# Halo 2 LookupRangeCheck Gadget -- Formal Verification (Kan Tactics)

This file formalizes the LookupRangeCheck gadget from Zcash's Halo 2
proving system, proving both soundness and completeness of:

1. **Running-sum range check**: decomposes a value `v` into `w` base-`b`
   digits and checks each lies in `[0, b)`.

2. **Short range check**: for `s < K`, checks `v` is in `[0, 2^s)` by
   verifying both `v` and `v * 2^(K - s)` lie in `[0, 2^K)`.

## Constraint: Kan-only tactics

Every `by` block uses exclusively tactics constructed by `kanExtend`
from `kan-tactics`.  No Mathlib dependency.  Arithmetic is done via
term-mode expressions routed through `kan_exact`, `kan_apply`, and
`kan_refine`.

## References

- `halo2_gadgets::utilities::lookup_range_check` (zcash/halo2)
- The Halo 2 Book, section on lookup arguments
- ZIP 224 (Orchard shielded protocol)
-/

set_option autoImplicit false

namespace Halo2Kan.LookupRangeCheck

-- ============================================================================
-- Part 0: Arithmetic Helpers (no Mathlib)
-- ============================================================================

/-- `b ^ (n + 1) = b * b ^ n` (flip of the definitional `b ^ n * b`). -/
theorem pow_succ' (b n : Nat) : b ^ (n + 1) = b * b ^ n := by
  kan_exact Nat.mul_comm (b ^ n) b

/-- `b ^ (m + n) = b ^ m * b ^ n` -/
theorem pow_add (b m : Nat) : (n : Nat) -> b ^ (m + n) = b ^ m * b ^ n
  | 0 => (Nat.mul_one (b ^ m)).symm
  | n + 1 =>
    show b ^ (m + n) * b = b ^ m * (b ^ n * b) from
    (pow_add b m n) ▸ Nat.mul_assoc (b ^ m) (b ^ n) b

/-- `0 < b -> 0 < b ^ n` -/
theorem pos_pow_of_pos {b : Nat} (hb : 0 < b) : (n : Nat) -> 0 < b ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (pos_pow_of_pos hb n) hb

/-- `0 < b` and `m ≤ n` imply `b ^ m ≤ b ^ n`. -/
theorem pow_le_pow_right {b : Nat} (hb : 0 < b) {m n : Nat} (h : m ≤ n) :
    b ^ m ≤ b ^ n := by
  kan_exact
    have hk : m + (n - m) = n := Nat.add_sub_cancel' h
    hk ▸ (pow_add b m (n - m)) ▸
      Nat.le_mul_of_pos_right (b ^ m) (pos_pow_of_pos hb (n - m))

/-- `b ^ (m * n) = (b ^ m) ^ n` -/
theorem pow_mul (b m : Nat) : (n : Nat) -> b ^ (m * n) = (b ^ m) ^ n
  | 0 => rfl
  | n + 1 =>
    show b ^ (m * n + m) = (b ^ m) ^ n * b ^ m from
    (pow_add b (m * n) m) ▸ congrArg (· * b ^ m) (pow_mul b m n)

/-- If `a < b` and `0 < c`, then `a * c < b * c`. -/
theorem mul_lt_mul_right' {a b c : Nat} (hab : a < b) (hc : 0 < c) :
    a * c < b * c := by
  kan_exact Nat.mul_lt_mul_of_pos_right hab hc

-- ============================================================================
-- Part 1: Base Decomposition
-- ============================================================================

/-- Evaluate a list of base-`b` digits (least-significant first).

    `evalDigits b [a_0, a_1, ..., a_{n-1}] = a_0 + b*a_1 + b^2*a_2 + ...` -/
def evalDigits (b : Nat) : List Nat -> Nat
  | [] => 0
  | d :: ds => d + b * evalDigits b ds

/-- Decompose `v` into `w` base-`b` digits (least-significant first). -/
def baseDecomp (b : Nat) : Nat -> Nat -> List Nat
  | 0, _ => []
  | w + 1, v => (v % b) :: baseDecomp b w (v / b)

@[simp] theorem evalDigits_nil {b : Nat} : evalDigits b [] = 0 := by kan_rfl

@[simp] theorem evalDigits_cons {b : Nat} (d : Nat) (ds : List Nat) :
    evalDigits b (d :: ds) = d + b * evalDigits b ds := by kan_rfl

@[simp] theorem baseDecomp_zero {b : Nat} (v : Nat) :
    baseDecomp b 0 v = [] := by kan_rfl

@[simp] theorem baseDecomp_succ {b : Nat} (w v : Nat) :
    baseDecomp b (w + 1) v = (v % b) :: baseDecomp b w (v / b) := by kan_rfl

/-- The length of `baseDecomp b w v` is exactly `w`. -/
theorem baseDecomp_length (b : Nat) : (w v : Nat) -> (baseDecomp b w v).length = w
  | 0, _ => rfl
  | w + 1, v => congrArg Nat.succ (baseDecomp_length b w (v / b))

/-- Every digit produced by `baseDecomp` is strictly less than `b`. -/
theorem mem_baseDecomp_lt {b : Nat} (hb : 0 < b) :
    (w v d : Nat) -> d ∈ baseDecomp b w v -> d < b
  | 0, _, d, hd => absurd hd (List.not_mem_nil d)
  | w + 1, v, d, hd =>
    have hd' : d ∈ (v % b :: baseDecomp b w (v / b)) := baseDecomp_succ w v ▸ hd
    (List.mem_cons.mp hd').elim
      (fun heq : d = v % b => heq.symm ▸ Nat.mod_lt v hb)
      (fun hmem => mem_baseDecomp_lt hb w (v / b) d hmem)

/-- Evaluating the base decomposition recovers the original value. -/
theorem evalDigits_baseDecomp {b : Nat} (hb : 0 < b) :
    (w v : Nat) -> v < b ^ w -> evalDigits b (baseDecomp b w v) = v
  | 0, 0, _ => rfl
  | 0, _ + 1, hv => absurd (Nat.le_of_succ_le_succ hv) (Nat.not_succ_le_zero _)
  | w + 1, v, hv =>
    have hv' : v / b < b ^ w :=
      Nat.div_lt_of_lt_mul (pow_succ' b w ▸ hv)
    have ih := evalDigits_baseDecomp hb w (v / b) hv'
    show v % b + b * evalDigits b (baseDecomp b w (v / b)) = v from
    ih.symm ▸ (Nat.add_comm (v % b) (b * (v / b))).trans (Nat.div_add_mod v b)

/-- If every digit is less than `b`, the sum is less than `b ^ length`.

    Core soundness argument: lookup-constraining each word to `[0, b)`
    forces the reconstructed value below `b ^ w`. -/
theorem evalDigits_lt_pow {b : Nat} (hb : 0 < b) :
    (ds : List Nat) -> (∀ d ∈ ds, d < b) ->
    evalDigits b ds < b ^ ds.length
  | [], _ => Nat.zero_lt_one
  | d :: ds, hds =>
    have hd := hds d (List.mem_cons_self d ds)
    have hds' := fun x (hx : x ∈ ds) => hds x (List.mem_cons_of_mem d hx)
    have ih := evalDigits_lt_pow hb ds hds'
    -- d + b*e < b + b*e = b*(e+1) ≤ b*b^n = b^n*b = b^(n+1)
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_right hd (b * evalDigits b ds))
      (Nat.le_trans
        (Nat.le_of_eq
          ((Nat.add_comm b (b * evalDigits b ds)).trans
            (Nat.mul_succ b (evalDigits b ds)).symm))
        (Nat.le_trans
          (Nat.mul_le_mul_left b ih)
          (Nat.le_of_eq (Nat.mul_comm b (b ^ ds.length)))))

-- ============================================================================
-- Part 2: Running-Sum Range Check
-- ============================================================================

/-- A strict running-sum decomposition of `v` into `w` base-`b` words.

    Captures the Halo 2 constraint system for `LookupRangeCheck`:
    - `words` are the K-bit chunks at each running-sum step
    - `len_eq` ensures exactly `w` steps
    - `word_bound` encodes the lookup constraint (each word in `[0, b)`)
    - `eval_eq` ties the decomposition back to the original value -/
structure StrictDecomp (b w v : Nat) where
  words : List Nat
  len_eq : words.length = w
  word_bound : ∀ d ∈ words, d < b
  eval_eq : evalDigits b words = v

/-- **Soundness of the running-sum range check.**

    If the circuit accepts (all lookups pass, `z_w = 0`), then `v < b^w`. -/
theorem soundness_runsum {b w v : Nat} (hb : 0 < b)
    (d : StrictDecomp b w v) : v < b ^ w := by
  kan_exact
    match d with
    | ⟨words, hlen, hbound, heval⟩ =>
      heval ▸ hlen ▸ evalDigits_lt_pow hb words hbound

/-- **Completeness of the running-sum range check.**

    Every value below `b^w` has a valid decomposition. -/
def completeness_runsum {b w v : Nat} (hb : 0 < b) (hv : v < b ^ w) :
    StrictDecomp b w v where
  words := baseDecomp b w v
  len_eq := baseDecomp_length b w v
  word_bound := fun d hd => mem_baseDecomp_lt hb w v d hd
  eval_eq := evalDigits_baseDecomp hb w v hv

-- ============================================================================
-- Part 3: Short Range Check
-- ============================================================================

private theorem pow_split {s K : Nat} (hs : s ≤ K) :
    2 ^ K = 2 ^ s * 2 ^ (K - s) :=
  (congrArg (2 ^ ·) (Nat.add_sub_cancel' hs).symm).trans (pow_add 2 s (K - s))

/-- **Soundness of the short range check.**

    If `e` passes both lookups (`e < 2^K` and `e * 2^{K-s} < 2^K`),
    then `e < 2^s`.  The first lookup prevents modular wrap-around. -/
theorem soundness_short {K s e : Nat} (hs : s ≤ K)
    (_he_lookup : e < 2 ^ K) (he_shift : e * 2 ^ (K - s) < 2 ^ K) :
    e < 2 ^ s := by
  kan_exact
    -- 2^K = 2^s * 2^(K-s), so he_shift : e * 2^(K-s) < 2^s * 2^(K-s)
    have : e * 2 ^ (K - s) < 2 ^ s * 2 ^ (K - s) := pow_split hs ▸ he_shift
    Nat.lt_of_mul_lt_mul_right this

/-- **Completeness of the short range check.**

    If `e < 2^s` and `s ≤ K`, both lookup constraints hold. -/
theorem completeness_short {K s e : Nat} (hs : s ≤ K) (he : e < 2 ^ s) :
    e < 2 ^ K ∧ e * 2 ^ (K - s) < 2 ^ K := by
  kan_constructor
  · -- e < 2^s ≤ 2^K since s ≤ K
    kan_exact Nat.lt_of_lt_of_le he (pow_le_pow_right (Nat.zero_lt_succ 1) hs)
  · -- e * 2^(K-s) < 2^s * 2^(K-s) = 2^K
    kan_exact (pow_split hs).symm ▸
      mul_lt_mul_right' he (pos_pow_of_pos (Nat.zero_lt_succ 1) (K - s))

-- ============================================================================
-- Part 4: Halo 2 Instantiation (K = 10, Pallas field)
-- ============================================================================

/-- The Halo 2 lookup table bit-width (the Sinsemilla constant). -/
def K : Nat := 10

private theorem two_mul_eq (n : Nat) : 2 * n = n + n :=
  (Nat.succ_mul 1 n).trans (congrArg (· + n) (Nat.one_mul n))

/-- The short range check multiplication never wraps in the Pallas field.

    Since `e < 2^K = 1024`, the product `e * 2^{K-s}` is at most
    `1023 * 1024 < 2^20`, far below the Pallas characteristic
    `p ~ 2^254`. -/
theorem halo2_short_no_wrap {p : Nat} (hp : 2 ^ (2 * K) < p)
    {e : Nat} (he : e < 2 ^ K) {s : Nat} (_hs : s ≤ K) :
    e * 2 ^ (K - s) < p := by
  kan_exact
    have hKK : 2 ^ K * 2 ^ K = 2 ^ (2 * K) :=
      ((pow_add 2 K K).symm.trans (congrArg (2 ^ ·) (two_mul_eq K).symm))
    Nat.lt_trans
      (Nat.lt_of_lt_of_le
        (mul_lt_mul_right' he (pos_pow_of_pos (Nat.zero_lt_succ 1) (K - s)))
        (Nat.mul_le_mul_left (2 ^ K)
          (pow_le_pow_right (Nat.zero_lt_succ 1) (Nat.sub_le K s))))
      (hKK ▸ hp)

/-- The standard Halo 2 range check equivalence.

    `v < (2^K)^w ↔ v < 2^{K*w}`. -/
theorem halo2_range_equiv (w v : Nat) :
    v < (2 ^ K) ^ w ↔ v < 2 ^ (K * w) := by
  kan_constructor
  · kan_intro h
    kan_exact (pow_mul 2 K w).symm ▸ h
  · kan_intro h
    kan_exact (pow_mul 2 K w) ▸ h

end Halo2Kan.LookupRangeCheck
