import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import LeanSharp.Theory.Convergence
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Toy Application of ZSharp

In this file, we demonstrate that our abstract definitions in `W d`
can be evaluated on concrete Euclidean vectors.

We use `d = 2` and a simple quadratic landscape:
$L(w_0, w_1) = w_0^2 + w_1^2$.
-/

namespace LeanSharp.Toy

open BigOperators

-- We work in 2D space
local notation "W2" => W 2

-- Define a simple 2D quadratic loss function
noncomputable def L_toy (w : W2) : ℝ :=
  let w0 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 0
  let w1 := (WithLp.equiv 2 (Fin 2 → ℝ) w) 1
  w0^2 + w1^2

/-- We evaluate the gradient of L_toy explicitly.
    ∇L_toy(w) = [2w_0, 2w_1] -/
noncomputable def exact_gradient_toy (w : W2) : W2 :=
  WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun i =>
    2 * (WithLp.equiv 2 (Fin 2 → ℝ) w) i

-- Now let's try to evaluate ZSharp on a specific vector: w = [1, 3]
noncomputable def w_init : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 1 else 3)

/-- Compute the toy exact gradient of w_init, which should be [2, 6]. -/
theorem exact_gradient_w_init :
    exact_gradient_toy w_init =
      (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then 2 else 6) := by
  unfold exact_gradient_toy w_init
  ext i
  simp only [Equiv.apply_symm_apply]
  fin_cases i
  · norm_num
  · norm_num

end LeanSharp.Toy
