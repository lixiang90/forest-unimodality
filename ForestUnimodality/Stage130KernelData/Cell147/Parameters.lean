import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-3177163259324147095412627/2000000000000000000000000)
  B := (19728266257412310769048247/200000000000000000000000000)
  C := (567014692504181727454593/125000000000000000000000000)
  dδ := (62956487800988100711485629/1000000000000000000000000000)
  dM := (2113027089947057141766651/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1517257819332736401563011/125000000000000000000000), (14816859943780333885854361/10000000000000000000000000), (3124285476299222708007619/200000000000000000000000), (5711183206954093094509517/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (94503/178928)
  hi := (28/53)
  vmin := (700/2809)
  damping := (700/2809)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell147
