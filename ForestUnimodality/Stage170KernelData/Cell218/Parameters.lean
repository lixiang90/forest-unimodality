import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell218
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (116)
  A := (-42192192100442318436037681 / 50000000000000000000000000)
  B := (46997281212505570557880219 / 1000000000000000000000000000)
  C := (19290492757371488496964673 / 100000000000000000000000000)
  dδ := (32961022319816485337540257 / 1000000000000000000000000000)
  dM := (3127149890571100988335973 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(98563609725140857165115449 / 10000000000000000000000000), (42289427451071745167610061 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643 / 1188)
  hi := (6 / 11)
  vmin := (30 / 121)
  damping := (30 / 121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell218
