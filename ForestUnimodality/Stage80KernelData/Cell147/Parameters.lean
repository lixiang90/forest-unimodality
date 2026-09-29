import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (2537359427983143284102141/5000000000000000000000000)
  B := (50943992001296040106339547/1000000000000000000000000000)
  C := (65500191037127265814010713/10000000000000000000000000000)
  dδ := (11923021757825159883115163/100000000000000000000000000)
  dM := (2807290727180008094859831/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11199704180240501738552439/10000000000000000000000000), (31102343262955978175909877/5000000000000000000000000), (500849415882919535292217/15625000000000000000000)]
  retention := ![(4/5), (7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94453/178928)
  hi := (47239/89464)
  vmin := (1994666775/8003807296)
  damping := (1994666775/8003807296)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell147
