import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (-21800158398170992434472737/100000000000000000000000000)
  B := (83198096139103575041851/781250000000000000000000)
  C := (14875549801396459673186179/2500000000000000000000000000)
  dδ := (6468851278014250971715171/50000000000000000000000000)
  dM := (1282387524015535240629049/500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5213380329321470441072961/1000000000000000000000000), (12655012050627558295445851/1000000000000000000000000), (8895094615214766520239209/500000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11153/21528)
  hi := (22331/43056)
  vmin := (462809975/1853819136)
  damping := (462809975/1853819136)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell107
