/-
MachLib.RingTest — coverage tests for `mach_ring` v1.

Each `example` here mirrors a ring-blocked obligation in
`monogate-engine/proofs/Proofs/`. A green build means the engine's
corresponding `sorry`s will close once their `by sorry` is replaced
with `by mach_ring`.

Engine theorems covered (per
`monogate-engine/proofs/Proofs/README.md`):

  Vec3.lerp_endpoint_at_zero
  Mat4.translate_then_transform_shifts_x
  Mat4.scale_then_transform_x
  Mat4.rotation_z_preserves_z
  Mat4.rotation_x_preserves_x
  Mat4.rotation_y_preserves_y
  MulMat4.mul_mat4_identity_left            (one cell — extends to all 16)
  MulMat4.mul_mat4_identity_right           (one cell — extends to all 16)
  MulMat4.mul_mat4_translation_compose_03
  ParticlesIntegrate.verlet_step_zero_accel_extrapolates

Out of scope for v1 (genuinely need polynomial reflection):

  Vec3.vec3_cross_perp_a
  Vec3.vec3_cross_lagrange_witness
  MulQuat.mul_quat_norm_witness
  Mat4.rotation_*_orthonormal_witness         (needs `linear_combination`)
-/

import MachLib.Ring

namespace MachLibTest.Ring

open MachLib MachLib.Real

/-- Mirrors `Vec3.lerp_endpoint_at_zero`: `a + (b - a) * 0 = a`. -/
example (a b : Real) : a + (b - a) * 0 = a := by mach_ring

/-- Mirrors `Mat4.translate_then_transform_shifts_x`:
    `1*x + 0*py + 0*pz + tx - (x + tx) = 0`. -/
example (tx x : Real) :
    let m00 : Real := 1
    let m01 : Real := 0
    let m02 : Real := 0
    let m03 : Real := tx
    let py  : Real := 0
    let pz  : Real := 0
    let result_x : Real := m00 * x + m01 * py + m02 * pz + m03
    let expected_x : Real := x + tx
    result_x - expected_x = 0 := by
  mach_ring

/-- Mirrors `Mat4.scale_then_transform_x`:
    `sx*x + 0*py + 0*pz + 0 - sx*x = 0`. -/
example (sx x : Real) :
    let m00 : Real := sx
    let m01 : Real := 0
    let m02 : Real := 0
    let m03 : Real := 0
    let py  : Real := 0
    let pz  : Real := 0
    let result_x : Real := m00 * x + m01 * py + m02 * pz + m03
    let expected_x : Real := sx * x
    result_x - expected_x = 0 := by
  mach_ring

/-- Mirrors `Mat4.rotation_z_preserves_z`:
    `0*px + 0*py + 1*z + 0 - z = 0`. -/
example (z : Real) :
    let m20 : Real := 0
    let m21 : Real := 0
    let m22 : Real := 1
    let m23 : Real := 0
    let px  : Real := 0
    let py  : Real := 0
    let result_z : Real := m20 * px + m21 * py + m22 * z + m23
    let expected_z : Real := z
    result_z - expected_z = 0 := by
  mach_ring

/-- Mirrors `Mat4.rotation_x_preserves_x` (same shape as Mat4.translate_then). -/
example (x : Real) :
    let m00 : Real := 1
    let m01 : Real := 0
    let m02 : Real := 0
    let m03 : Real := 0
    let py  : Real := 0
    let pz  : Real := 0
    let result_x : Real := m00 * x + m01 * py + m02 * pz + m03
    let expected_x : Real := x
    result_x - expected_x = 0 := by
  mach_ring

/-- Mirrors `Mat4.rotation_y_preserves_y`. -/
example (y : Real) :
    let m10 : Real := 0
    let m11 : Real := 1
    let m12 : Real := 0
    let m13 : Real := 0
    let px  : Real := 0
    let pz  : Real := 0
    let result_y : Real := m10 * px + m11 * y + m12 * pz + m13
    let expected_y : Real := y
    result_y - expected_y = 0 := by
  mach_ring

/-- Mirrors `MulMat4.mul_mat4_identity_left` (canonical cell):
    `1 * a00 + 0 * b10 + 0 * c20 + 0 * d30 = a00`. -/
example (a b c d : Real) :
    1 * a + 0 * b + 0 * c + 0 * d = a := by
  mach_ring

/-- Mirrors `MulMat4.mul_mat4_identity_right` (right-multiply by I):
    `a00 * 1 + a01 * 0 + a02 * 0 + a03 * 0 = a00`. -/
example (a b c d : Real) :
    a * 1 + b * 0 + c * 0 + d * 0 = a := by
  mach_ring

/-- Mirrors `MulMat4.mul_mat4_translation_compose_03`:
    composing two translations sums their components in the
    last column (e.g. `1*0 + 0*0 + 0*0 + tx*1 = tx`). -/
example (tx : Real) :
    1 * 0 + 0 * 0 + 0 * 0 + tx * 1 = tx := by
  mach_ring

/-- Direct test of the swapped-pair shape: a Forge matrix-cell
    witness with addends in opposite order on the two sides. -/
example (a b : Real) : (a + b) + -(b + a) = 0 := by mach_ring

/-- Mirrors `ParticlesIntegrate.verlet_step_zero_accel_extrapolates`:
    with zero acceleration the integrator reduces to `pos + vel * dt`,
    i.e. the `0 * dt * dt` term drops out. -/
example (dt : Real) : 0 * dt * dt = 0 := by mach_ring

end MachLibTest.Ring
