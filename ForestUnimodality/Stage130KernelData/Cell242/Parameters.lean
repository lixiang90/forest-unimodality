import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell242
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 18
  A := (18321944316673078768431537/100000000000000000000000000)
  B := (9848966542714911870382011/500000000000000000000000000)
  C := (4391410311389204457199753/125000000000000000000000000)
  dδ := (22634930946245093719149111/1000000000000000000000000000)
  dM := (18813377126601567605398979/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(22903260459125038828176457/5000000000000000000000000), (11986572917497986257018283/10000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107/156)
  hi := (9/13)
  vmin := (36/169)
  damping := (1440000000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell242
