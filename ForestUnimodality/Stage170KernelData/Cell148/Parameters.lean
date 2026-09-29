import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (137)
  A := (-3557292524479886399717543 / 2000000000000000000000000)
  B := (39052799738212101710033153 / 500000000000000000000000000)
  C := (-6619835460908412693575853 / 20000000000000000000000000000)
  dδ := (578856699946098639253389 / 12500000000000000000000000)
  dM := (2461411961759790018033911 / 4000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(6461912310724802210870621 / 250000000000000000000000), (2186554739012764798644639 / 20000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (1 / 2)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell148
