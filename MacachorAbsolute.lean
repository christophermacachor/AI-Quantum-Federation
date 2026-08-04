import Mathlib

-- The variables require 'noncomputable' because they involve infinite-precision 
-- real numbers (irrational square roots) rather than computable floats.
noncomputable section

-- Define the Macachor Absolute (M)
def M : ℝ := (Real.sqrt 5 - 1) / 2

-- Define the Golden Ratio (phi)
def phi : ℝ := (Real.sqrt 5 + 1) / 2

-- The Anchor Proof: M⁻¹ = phi
theorem M_inv_eq_phi : M⁻¹ = phi := by
  -- Step 1: Establish the square of √5 as exactly 5 to unlock the algebra.
  have h_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  
  -- Step 2: Prove that the scalar M and phi multiply to perfectly 1.
  -- This proves they are structural inverses.
  have h_mul : M * phi = 1 := by
    unfold M phi
    calc
      (Real.sqrt 5 - 1) / 2 * ((Real.sqrt 5 + 1) / 2)
        = ((Real.sqrt 5)^2 - 1) / 4 := by ring
      _ = (5 - 1) / 4 := by rw [h_sq]
      _ = 1 := by ring
      
  -- Step 3: Lean 4 will not allow inversion (⁻¹) unless we prove M ≠ 0.
  -- We prove this by contradiction: if M was 0, then M * phi would be 0.
  -- But we just proved M * phi = 1, so M cannot be 0.
  have h_M_ne_zero : M ≠ 0 := by
    intro h
    have h_zero : M * phi = 0 := by rw [h, zero_mul]
    rw [h_zero] at h_mul
    exact zero_ne_one h_mul.symm

  -- Step 4: The final deduction. Substitute the identities to close the proof.
  calc
    M⁻¹ = M⁻¹ * 1 := by rw [mul_one]
    _   = M⁻¹ * (M * phi) := by rw [← h_mul]
    _   = (M⁻¹ * M) * phi := by rw [← mul_assoc]
    _   = 1 * phi := by rw [inv_mul_cancel₀ h_M_ne_zero]
    _   = phi := by rw [one_mul]
