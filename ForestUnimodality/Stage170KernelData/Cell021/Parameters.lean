import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (26)
  A := (15624799718012944872214121 / 100000000000000000000000000)
  B := (11292765415371082762807653 / 1000000000000000000000000000)
  C := (-18705389956513853583208729 / 1000000000000000000000000000)
  dδ := (11919589797473663025928481 / 1000000000000000000000000000)
  dM := (52200195812995614421531121 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(530504050288056819284499 / 156250000000000000000000), (43653277305032140986895683 / 10000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell021
