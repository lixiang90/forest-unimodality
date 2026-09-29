import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell172
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-3756150437648554476481877/2000000000000000000000000)
  B := (2664312008774830653479171/20000000000000000000000000)
  C := (1473250984341524473172913/250000000000000000000000000)
  dδ := (75192923926186733263321571/1000000000000000000000000000)
  dM := (17103787704028485319729391/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15534177878485532886543297/1000000000000000000000000), (50518456982701380297839933/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11953/22578)
  hi := (31883/60208)
  vmin := (903085975/3625003264)
  damping := (903085975/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell172
