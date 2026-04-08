# halo2-kan

Formal verification of Halo 2 circuit gadgets in Lean 4, using
exclusively tactics derived from Kan extensions.

Every tactic-mode proof routes through the single `kanExtend` entry
point from [kan-tactics](https://github.com/MavenRain/kan-tactics).
No Mathlib dependency.

## Status

**LookupRangeCheck** gadget: soundness and completeness proved.

See `EXPLAINER.md` for a detailed walkthrough of the gadget, the proof
strategy, and how this connects to the broader formalization effort.

## Structure

```
Halo2Kan/
  LookupRangeCheck.lean   -- Definitions and proofs (Kan-only)
EXPLAINER.md              -- Non-technical explainer
```

### Main results (`Halo2Kan.LookupRangeCheck`)

| Theorem | Statement |
|---------|-----------|
| `soundness_runsum` | Strict running-sum decomposition implies `v < b^w` |
| `completeness_runsum` | `v < b^w` implies a valid decomposition exists |
| `soundness_short` | Both short-check lookups pass implies `e < 2^s` |
| `completeness_short` | `e < 2^s` implies both lookups pass |
| `halo2_short_no_wrap` | Field multiplication does not wrap for Pallas |

### Constraint: Kan-only tactics

The following tactics (all instances of `kanExtend`) are the only
tactic-mode invocations permitted in proofs:

| Tactic | Kan extension kind |
|---|---|
| `kan_rfl` | Identity |
| `kan_exact e` | Identity |
| `kan_apply e` | Precomposition |
| `kan_refine e` | Precomposition |
| `kan_intro x` | Adjunction unit |
| `kan_intros` | Adjunction unit |
| `kan_rw [h1, <-h2]` | Transport |
| `kan_calc_trans b` | Transport |
| `kan_simp` | Normalize |
| `kan_dsimp` | Normalize |
| `kan_simp_only [h]` | Normalize |
| `kan_constructor` | Colimit injection |
| `kan_use e` / `kan_exists e` | Colimit injection |
| `kan_cases h` / `kan_rcases h` | Colimit decomposition |
| `kan_induction n` | Initial algebra |

Arithmetic that halo2-formal handles with `omega`, `linarith`, `ring`,
and `positivity` is instead carried out in term mode and passed through
`kan_exact`.

## Building

Requires Lean 4.  After cloning:

```sh
lake update    # fetch kan-tactics
lake build
```

## License

Dual-licensed under MIT OR Apache-2.0 at your option.

## Context

This work supports the Zcash Community Grants proposal
"Formal Verification of Halo 2 in Lean 4"
([ZcashCommunityGrants/zcashcommunitygrants#244](https://github.com/ZcashCommunityGrants/zcashcommunitygrants/issues/244)).
