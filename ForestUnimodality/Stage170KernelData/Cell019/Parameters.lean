import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (31)
  A := (18278380880864176672773169 / 100000000000000000000000000)
  B := (34293047794073127677860757 / 5000000000000000000000000000)
  C := (-5804552752466097392813893 / 500000000000000000000000000)
  dδ := (38232944409452638938329283 / 5000000000000000000000000000)
  dM := (10245646598753553171219817 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(2062162794541754635702091 / 20000000000000000000000), (49293861377476446250511799 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39 / 140)
  hi := (2 / 7)
  vmin := (3939 / 19600)
  damping := (393900000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell019
