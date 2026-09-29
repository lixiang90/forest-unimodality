import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 28
  A := (8509336521125094255246779/50000000000000000000000000)
  B := (3281460222148722960522349/200000000000000000000000000)
  C := (-39152039826509429931711281/1000000000000000000000000000)
  dδ := (3545850637962489476651129/200000000000000000000000000)
  dM := (5837333521543285009755553/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(48826782828361664501315431/50000000000000000000000000), (14024422677690377980752601/10000000000000000000000000), (37534432663388734852105699/5000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/85)
  hi := (89/255)
  vmin := (1624/7225)
  damping := (2598400000000000000000000000000000000000000/28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell012
