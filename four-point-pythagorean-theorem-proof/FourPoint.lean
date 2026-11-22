import Std

/-!
A coordinate companion to the four-point proof of Pythagoras. Check with Lean 4.35.0:
    lean FourPoint.lean

This file does not formalize the area argument on page 1 of the paper. It has no areas,
no distances to lines, and no square. It checks the coordinate computation on page 2.

The scalar field is an arbitrary complete ordered field. Segment length is an abstract
function, calibrated on a ruler and unchanged by reflection in lines through the origin.
No distance formula is assumed, but one is implied. Mirror images are defined with
(-t, 1) perpendicular to (1, t), so the reflections are the Euclidean ones. They preserve
x^2 + y^2, and any length with these two properties is the Euclidean length. The
Pythagorean content of the theorem enters through this hypothesis.
-/

namespace FourPoint

open Std Lean.Grind

variable {R : Type u} [Field R] [LE R] [LT R] [LawfulOrderLT R]
  [IsLinearOrder R] [OrderedRing R]

/-- Ruler calibration and equality of lengths of mirror images.
For the mirror line y = t * x, the first equation puts the segment joining the
two points perpendicular to the mirror; the second puts its midpoint on it.
Perpendicular direction to (1,t) is defined by quarter-turn as (-t,1).
This is the dot-product notion of perpendicularity, so `reflect` describes
Euclidean reflections. -/
structure RulerLength (R : Type u) [Field R] [LE R] where
  length : R → R → R
  on_ruler : ∀ r, 0 ≤ r → length r 0 = r
  reflect : ∀ t x y x' y',
    x - x' = -t * (y - y') → y + y' = t * (x + x') →
    length x y = length x' y'

/-- Dedekind completeness: every inhabited, bounded-above set has a supremum. -/
def HasSuprema (R : Type u) [LE R] : Prop :=
  ∀ S : R → Prop, (∃ x, S x) → (∃ z, ∀ x, S x → x ≤ z) →
    ∃ s, (∀ x, S x → x ≤ s) ∧ (∀ z, (∀ x, S x → x ≤ z) → s ≤ z)

/-- A one-sided Lipschitz estimate suffices for a zero between opposite signs.
The supremum of the nonpositive set cannot have either strict sign. -/
private theorem zeroOnUnitInterval (complete : HasSuprema R) (f : R → R)
    (L : R) (hL : 0 < L) (low : f 0 < 0) (high : 0 < f 1)
    (bound : ∀ x y, 0 ≤ x → x ≤ y → y ≤ 1 → f y - f x ≤ L * (y - x)) :
    ∃ t, 0 < t ∧ t < 1 ∧ f t = 0 := by
  let S := fun x => 0 ≤ x ∧ x ≤ (1:R) ∧ f x ≤ 0
  have zeroMem : S 0 := by dsimp [S]; grind
  obtain ⟨s, upper, least⟩ := complete S ⟨0, zeroMem⟩ ⟨1, fun _ h => h.2.1⟩
  have hs0 := upper 0 zeroMem
  have hs1 := least 1 (fun _ h => h.2.1)
  let y := s - f s * L⁻¹
  have inv := Field.mul_inv_cancel (Preorder.ne_of_gt hL)
  have step : L * y = L * s - f s := by unfold y; grind
  have rightBound := bound s 1 hs0 hs1 (by grind)
  have hy1 : y ≤ 1 := (Field.IsOrdered.mul_le_mul_iff_of_pos_left hL).mp (by grind)
  have root : f s = 0 := by
    rcases LinearOrder.trichotomy (f s) 0 with negative | eq | positive
    · have hsy : s < y := (Field.IsOrdered.mul_lt_mul_iff_of_pos_left hL).mp (by grind)
      have near := bound s y hs0 (Preorder.le_of_lt hsy) hy1
      have member : S y := by dsimp [S]; grind
      have := upper y member
      grind
    · exact eq
    · have hys : y < s := (Field.IsOrdered.mul_lt_mul_iff_of_pos_left hL).mp (by grind)
      have upperY : ∀ x, S x → x ≤ y := by
        intro x hx
        have near := bound x s hx.1 (upper x hx) hs1
        have sign := hx.2.2
        exact (Field.IsOrdered.mul_le_mul_iff_of_pos_left hL).mp (by grind)
      have := least y upperY
      grind
  exact ⟨s, by grind, by grind, root⟩

/-- The slope t of the bisector. Since c = a + b * t, finding t is equivalent to
finding c > 0 with c^2 = a^2 + b^2, so this is where completeness supplies that
square root. -/
private theorem bisectorSlope (complete : HasSuprema R) (a b : R)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ t, 0 < t ∧ t < 1 ∧ b * t^2 + 2 * a * t - b = 0 := by
  let f := fun t : R => b * t^2 + 2 * a * t - b
  apply zeroOnUnitInterval complete f (2 * (a + b)) (by grind)
  · dsimp [f]; grind
  · dsimp [f]; grind
  · intro x y hx hxy hy
    have factor : b * (x + y) ≤ b * 2 :=
      OrderedRing.mul_le_mul_of_nonneg_left (by grind) (Preorder.le_of_lt hb)
    have product := OrderedRing.mul_le_mul_of_nonneg_right factor (show 0 ≤ y - x by grind)
    dsimp [f]; grind

/-- The four signed-height readings from the table on page 2 of the paper.
The first two coordinates are horizontal
and vertical displacements. The last is vertical displacement after reflecting
the corner in the diagonal (1,t). Reflection fixes the first and third corners,
and interchanges the second and fourth. -/
private def sumCorners (t : R) (f : R → R → R → R) : R :=
  f 1 t t + f (-t) 1 (-1) + f (-1) (-t) (-t) + f t (-1) 1

/-- The algebra of the paper's four-corner argument, in coordinates.
The hypotheses are the two mirror conditions. They agree with the page-1 area
equation b * X - a * Y = c * Z at the two neighboring corners, but that area
equation is not derived here. The opposite corners reverse all three readings.
The hypotheses alone already give the result, since
c^2 - a^2 - b^2 = (c + a) * (c - a - b * t) + b * (t * (a + c) - b).
The proof below instead squares and sums the four corner equations as on page 1. -/
theorem four_area_identity (a b c t : R)
    (first : b - a * t = c * t) (second : -b * t - a = -c) :
    a^2 + b^2 = c^2 := by
  let K := sumCorners t (fun x _ _ => x^2)
  have sameY : sumCorners t (fun _ y _ => y^2) = K := by
    unfold K sumCorners
    grind
  have sameZ : sumCorners t (fun _ _ z => z^2) = K := by
    unfold K sumCorners
    grind
  have mixed : sumCorners t (fun x y _ => x * y) = 0 := by
    unfold sumCorners
    grind
  have areaSquares :
      sumCorners t (fun x y _ => (b * x - a * y)^2) =
      sumCorners t (fun _ _ z => (c * z)^2) := by
    have cornersOpposite₁ : b * (-1) - a * (-t) = c * (-t) := by grind
    have cornersOpposite₂ : b * t - a * (-1) = c * 1 := by grind
    unfold sumCorners
    simp only [Semiring.mul_one, Ring.mul_neg] at *
    grind
  clear first second
  have expanded :
      sumCorners t (fun x y _ => (b * x - a * y)^2) =
      b^2 * K + a^2 * sumCorners t (fun _ y _ => y^2) -
        2 * a * b * sumCorners t (fun x y _ => x * y) := by
    unfold K sumCorners
    grind
  have hypotenuse :
      sumCorners t (fun _ _ z => (c * z)^2) =
      c^2 * sumCorners t (fun _ _ z => z^2) := by
    unfold sumCorners
    grind
  rw [expanded, hypotenuse, sameY, sameZ, mixed] at areaSquares
  have positive : 0 < K := by
    have := OrderedRing.sq_nonneg (a := t)
    unfold K sumCorners
    grind
  have equalProducts : (a^2 + b^2) * K = c^2 * K := by grind
  have cancel := congrArg (fun w : R => w * K⁻¹) equalProducts
  simpa only [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_gt positive),
    Semiring.mul_one] using cancel

/-- All right triangles, placed with vertices (0,0), (a,0), (a,b).
The "length" on the right is the primitive length of the displacement (a,b).
The mirror construction gives the two equations that `four_area_identity` needs. -/
theorem pythagoras (complete : HasSuprema R) (ruler : RulerLength R)
    (a b : R) (ha : 0 < a) (hb : 0 < b) :
    a^2 + b^2 = (ruler.length a b)^2 := by
  -- Find the slope of the mirror that folds the hypotenuse onto the ruler.
  obtain ⟨t, ht, _, root⟩ := bisectorSlope complete a b ha hb
  let c := a + b * t
  have cpos : 0 < c := by
    have := OrderedRing.mul_pos hb ht
    unfold c
    grind
  have perpendicular : a - c = -t * (b - 0) := by unfold c; grind
  have midpoint : b + 0 = t * (a + c) := by unfold c; grind
  have measure : ruler.length a b = c :=
    (ruler.reflect t a b c 0 perpendicular midpoint).trans
      (ruler.on_ruler c (Preorder.le_of_lt cpos))
  rw [measure]
  apply four_area_identity a b c t
  · grind
  · grind

/-- The same theorem with all three sides expressed as ruler measurements. -/
theorem pythagoras_lengths (complete : HasSuprema R) (ruler : RulerLength R)
    (a b : R) (ha : 0 < a) (hb : 0 < b) :
    (ruler.length a 0)^2 + (ruler.length 0 b)^2 = (ruler.length a b)^2 := by
  have vertical := ruler.reflect 1 0 b b 0 (by grind) (by grind)
  rw [vertical, ruler.on_ruler a (Preorder.le_of_lt ha),
    ruler.on_ruler b (Preorder.le_of_lt hb)]
  exact pythagoras complete ruler a b ha hb

end FourPoint
