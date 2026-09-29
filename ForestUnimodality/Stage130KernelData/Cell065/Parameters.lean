import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 83
  A := (-6556568721088346879355413/5000000000000000000000000)
  B := (92091431869588624703482083/1000000000000000000000000000)
  C := (-37103042303316909923671663/100000000000000000000000000000)
  dδ := (33122882113984467022937963/500000000000000000000000000)
  dM := (2084233629901306034115649/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10518439288809954490488963/1000000000000000000000000), (13457376243237495927473901/500000000000000000000000), (22094814873346223293992807/500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (197/396)
  hi := (395/792)
  vmin := (39203/156816)
  damping := (39203/156816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell065
