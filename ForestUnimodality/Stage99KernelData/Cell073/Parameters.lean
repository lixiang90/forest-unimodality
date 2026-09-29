import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 63
  A := (-18751990514029313960975287/20000000000000000000000000)
  B := (90901380983861745921359443/1000000000000000000000000000)
  C := (1062656744472956194501323/625000000000000000000000000)
  dδ := (3097199656863329764178161/40000000000000000000000000)
  dM := (3111300984550020290106409/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(4171949433384877004016289/500000000000000000000000), (53642781866898282316924451/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5227/10302)
  hi := (3493/6868)
  vmin := (11788875/47169424)
  damping := (11788875/47169424)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell073
