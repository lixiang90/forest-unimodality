import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (41)
  A := (16898243566150828899097291 / 100000000000000000000000000)
  B := (13251273428671378820653537 / 1000000000000000000000000000)
  C := (-40618845451975152394119561 / 1000000000000000000000000000)
  dδ := (2794256582173161931881289 / 200000000000000000000000000)
  dM := (36306448342365235128475359 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(35078840521368546134794997 / 5000000000000000000000000), (86947126343975007500830543 / 10000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 51)
  hi := (97 / 255)
  vmin := (608 / 2601)
  damping := (608 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell063
