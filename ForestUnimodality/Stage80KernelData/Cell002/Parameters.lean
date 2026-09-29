import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 15
  A := (1904333083973986318504501/50000000000000000000000000)
  B := (1121807700237661825637403/40000000000000000000000000)
  C := (-7016981904522247293076731/200000000000000000000000000)
  dδ := (6549359007175798406963363/250000000000000000000000000)
  dM := (6804322152051713848332909/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(95445354741483012794844853/100000000000000000000000000), (30937893401238150126175697/10000000000000000000000000)]
  retention := ![(1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/140)
  hi := (19/70)
  vmin := (3811/19600)
  damping := (381100000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell002
