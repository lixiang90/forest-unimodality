import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell113.Parameters
import ForestUnimodality.BinomialMassData.Q109_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q109_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q109_209.Batch100_149
import ForestUnimodality.BinomialMassData.Q109_209.Batch150_199
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch000_049
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch050_099
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch100_149
import ForestUnimodality.BinomialMassData.Q4583_8778.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree000.table
  base := (729329542020352534115090751/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (707932533903107008566024660000000000000)
      linear := (-37374554255450585966980004000000000000)
      constant := (729329542020352534115090751000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree000.table
  base := (729329542020352534115090751/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (146)
      previous := (73)
      next := (73)
      square := (707932533903107008566024660000000000000)
      linear := (-37374554255450585966980004000000000000)
      constant := (729329542020352534115090751000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree001.table
  base := (12493677505245033752040973988424998657017/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-33887380014125698569908869113644000000000000)
      constant := (17472824843567262452500543823685139722789106464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree001.table
  base := (399438977878242873491843790590069312230741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-4986623388561978917544264230093568000000000000)
      constant := (2566204825156640984396471341227539944249996650287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49951131997237524299/100000000000000000000)
  directionHi := (499511319972375243/1000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree002.table
  base := (232666850974633753695514542965885801045157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-66142202123819060094194084672564000000000000)
      constant := (10198467362605175092246690050176945675453502917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree002.table
  base := (232304323129057254189201950196027214485757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-3244420255057468096460617129214236000000000000)
      constant := (498952651520268027034887302599523005041665224333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49951131997237524299/100000000000000000000)
  centralHi := (499511319972375243/1000000000000000000)
  directionLo := (70641568326381973429/100000000000000000000)
  directionHi := (7064156832638197343/10000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree003.table
  base := (145419942573032902445200967027393891281219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-98397024233512421618479300231484000000000000)
      constant := (6430341318611855800424521206006104565054927139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree003.table
  base := (29027559929302265619587574297951942710089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-4826632713927609887073146181730616000000000000)
      constant := (314491078048345925921374390480761051332252414205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70641568326381973429/100000000000000000000)
  centralHi := (7064156832638197343/10000000000000000000)
  directionLo := (1351842164293669383/1562500000000000000)
  directionHi := (86517898514794840513/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree004.table
  base := (48949056175167074924962352841607420731827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-130651846343205783142764515790404000000000000)
      constant := (4414268307421764708690583178600363489973870374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree004.table
  base := (97695253692528563592658935867278866061861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-19226535518393255033057025702740988000000000000)
      constant := (647638646632702690619325211092285149821878100127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1351842164293669383/1562500000000000000)
  centralHi := (86517898514794840513/100000000000000000000)
  directionLo := (99902263994475048599/100000000000000000000)
  directionHi := (499511319972375243/500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree005.table
  base := (3523981215846019368406733194331305902241/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-162906668452899144667049731349324000000000000)
      constant := (3293151279272436898841382585223835462315782420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree005.table
  base := (17583889435418058592500964377650280470629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-7991057631667893468298204286763376000000000000)
      constant := (161078803527441459448890250284573367642558888404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/100000000000000000000)
  centralHi := (499511319972375243/500000000000000000)
  directionLo := (22338825339777588329/20000000000000000000)
  directionHi := (55847063349443970823/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree006.table
  base := (53508995940349894625872104023954783387219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-195161490562592506191334946908244000000000000)
      constant := (2645229101664285583222027808173672893137113139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree006.table
  base := (26702151087398021452927260859596303180601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-9573270090538035258910733339279756000000000000)
      constant := (129424842935845071963320765198729015684719563538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/20000000000000000000)
  centralHi := (55847063349443970823/50000000000000000000)
  directionLo := (122354785467641920669/100000000000000000000)
  directionHi := (12235478546764192067/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree007.table
  base := (42185896711045970254517645619820006853903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-227416312672285867715620162467164000000000000)
      constant := (2260818537608490869349855688904765719385336943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree007.table
  base := (10526661252463054335677506416262223611989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-682988727514786349970811983171192000000000000)
      constant := (6774791997826824102869342768662591275143498108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122354785467641920669/100000000000000000000)
  centralHi := (12235478546764192067/10000000000000000000)
  directionLo := (26431654594170320281/20000000000000000000)
  directionHi := (66079136485425800703/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree008.table
  base := (34082040526511393059458627301039242197907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-259671134781979229239905378026084000000000000)
      constant := (2033849621861871638222990565975127138446775667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree008.table
  base := (34019300984834271558863267144936101898817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-12737695008278318840135791444312516000000000000)
      constant := (99582357960465063905693641717219787485069043473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26431654594170320281/20000000000000000000)
  centralHi := (66079136485425800703/50000000000000000000)
  directionLo := (141283136652763946859/100000000000000000000)
  directionHi := (7064156832638197343/5000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree009.table
  base := (13968172273768638484701641947285903970089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-291925956891672590764190593585004000000000000)
      constant := (1909236994924944537361336844861167142634915218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree009.table
  base := (27884703315881890603234772115242395394097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-14319907467148460630748320496828896000000000000)
      constant := (93515451964121564188276871906669989587268001793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141283136652763946859/100000000000000000000)
  centralHi := (7064156832638197343/5000000000000000000)
  directionLo := (74926697995856286449/50000000000000000000)
  directionHi := (149853395991712572899/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree010.table
  base := (23068438723553480200806509418401490466159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-324180779001365952288475809143924000000000000)
      constant := (1857261412618755203517860751162435505052291279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree010.table
  base := (5756172476357219163826378487146278920477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-47706359778055807264082548648035828000000000000)
      constant := (273008102534605887795127401859245606400909232156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74926697995856286449/50000000000000000000)
  centralHi := (149853395991712572899/100000000000000000000)
  directionLo := (39489837203746535761/25000000000000000000)
  directionHi := (31591869762997228609/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree011.table
  base := (19091911983146285891437306716677187258913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-2945748769512886891014553923164000000000000)
      constant := (15380529363081661739119422298464464600467593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree011.table
  base := (1905414953557795051740273232378704467709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-144498614751146646379945277701336000000000000)
      constant := (753882847027823781462370078682460033293045010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39489837203746535761/25000000000000000000)
  centralHi := (31591869762997228609/20000000000000000000)
  directionLo := (20708645336044101173/12500000000000000000)
  directionHi := (33133832537670561877/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree012.table
  base := (630925470566319381080376224089804383117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-388690423220752675337046240261764000000000000)
      constant := (1910379830324711228814566317671396631473341925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree012.table
  base := (15740189002310100453499622717699194118889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-19066544843758886002585907654378036000000000000)
      constant := (93668345506422740933561853038749498417052330041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20708645336044101173/12500000000000000000)
  centralHi := (33133832537670561877/20000000000000000000)
  directionLo := (6921431881183587241/4000000000000000000)
  directionHi := (86517898514794840513/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree013.table
  base := (12960985752686026550555312285646178921721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-420945245330446036861331455820684000000000000)
      constant := (1998667352595668411463312313616662741479695001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree013.table
  base := (12932085520832599654450557403888726825999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-61946271907887083379595310120683248000000000000)
      constant := (294076984550618386521370409309200140043509960893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6921431881183587241/4000000000000000000)
  centralHi := (86517898514794840513/50000000000000000000)
  directionLo := (180101367683509842641/100000000000000000000)
  directionHi := (90050683841754921321/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree014.table
  base := (422048879536063723765977465136744098313/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-453200067440139398385616671379604000000000000)
      constant := (2121353445081629481409830383111848973960253825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree014.table
  base := (10525823079671163536550041193595056352957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-453693260438758562934917668559404000000000000)
      constant := (2123859997454155882805928217997081656553514717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180101367683509842641/100000000000000000000)
  centralHi := (90050683841754921321/50000000000000000000)
  directionLo := (186900022015183962701/100000000000000000000)
  directionHi := (93450011007591981351/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree015.table
  base := (8467968812146870921201031081820755156371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-485454889549832759909901886938524000000000000)
      constant := (2275123739433921998666600082480372405985441651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree015.table
  base := (8445647595089778080082963728556756927167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-23813182220369311374423494811927176000000000000)
      constant := (111636638889113300593299280732718712267443504623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186900022015183962701/100000000000000000000)
  centralHi := (93450011007591981351/50000000000000000000)
  directionLo := (48364975587377339457/25000000000000000000)
  directionHi := (193459902349509357829/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree016.table
  base := (831711233130763699004125843076637891771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-517709711659526121434187102497444000000000000)
      constant := (2457464989960494308278086491427188958003592408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree016.table
  base := (6634094309086733792651779448802386877291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-76186184037718359495108071593330668000000000000)
      constant := (361815488315497264710049265189003995994481381137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48364975587377339457/25000000000000000000)
  centralHi := (193459902349509357829/100000000000000000000)
  directionLo := (99902263994475048599/50000000000000000000)
  directionHi := (199804527988950097199/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree017.table
  base := (158233933133878539409258606879663481891/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-549964533769219482958472318056364000000000000)
      constant := (2666415950913971840514859888434586577679384672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree017.table
  base := (5046309904147049376980439254966900977637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-26977607138109594955648552916959936000000000000)
      constant := (130878708873054778183372465737945997878603928053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/50000000000000000000)
  centralHi := (199804527988950097199/100000000000000000000)
  directionLo := (205953793343780364553/100000000000000000000)
  directionHi := (102976896671890182277/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree018.table
  base := (457705147746447076491622654900838278269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-582219355878912844482757533615284000000000000)
      constant := (2900416528476693849848724671279060134664545512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree018.table
  base := (3646612128602330225624432103450133487001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-28559819596979736746261081969476316000000000000)
      constant := (142380904007459140335826012099673266761438843369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205953793343780364553/100000000000000000000)
  centralHi := (102976896671890182277/50000000000000000000)
  directionLo := (211924704979145920289/100000000000000000000)
  directionHi := (21192470497914592029/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree019.table
  base := (1209694714947628393075099379112197436573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-1702144537364560127443331715164000000000000)
      constant := (8748504646872425692471522060001151779650666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree019.table
  base := (300782717635722968188897267489889918467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2596902)
      previous := (1298451)
      next := (1298451)
      square := (12591995980534564361363880627420000000000000)
      linear := (-250487801018143034932467681623208000000000000)
      constant := (1288506112967372638767880023362418375838180232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211924704979145920289/100000000000000000000)
  centralHi := (21192470497914592029/10000000000000000000)
  directionLo := (54432984122854844891/25000000000000000000)
  directionHi := (43546387298283875913/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree020.table
  base := (1313374239200904542136499696678660610021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-646729000098299567531327964733124000000000000)
      constant := (3438776668673528854792515466857100574106327301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree020.table
  base := (1301926293844877146523194776065696684439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-31724244514720020327486140074509076000000000000)
      constant := (168836763584035238915648151782704679146776017991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54432984122854844891/25000000000000000000)
  centralHi := (43546387298283875913/20000000000000000000)
  directionLo := (22338825339777588329/10000000000000000000)
  directionHi := (223388253397775883291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree021.table
  base := (64906382269439818424133833240374796187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-678983822207992929055613180292044000000000000)
      constant := (3741283280518459955948978243330328057361221735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree021.table
  base := (157282010438312601662881535307301913199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-679723611705921675879564676061744000000000000)
      constant := (3748974113728271244975537387108895509740891038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/10000000000000000000)
  centralHi := (223388253397775883291/100000000000000000000)
  directionLo := (14306552714129477771/6250000000000000000)
  directionHi := (228904843426071644337/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree022.table
  base := (-281376335717381526218250778301741556123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-5878005324939556120495028064884000000000000)
      constant := (33595437430549384340237410056474142596479194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree022.table
  base := (-71427473671118442765031687106450195373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530670000000000000000000000000000000000000000
      center := (7747782)
      previous := (3873891)
      next := (3873891)
      square := (37567855776636179623573230632220000000000000)
      linear := (-865008333036205882034161938335748000000000000)
      constant := (4948903168327069943182975242308312059857128072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14306552714129477771/6250000000000000000)
  centralHi := (228904843426071644337/100000000000000000000)
  directionLo := (234291576740863266811/100000000000000000000)
  directionHi := (58572894185215816703/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree023.table
  base := (-272260360502289049366436297543064948991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-743493466427379652104183611409884000000000000)
      constant := (4409510523811035016629024947579298899815620645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree023.table
  base := (-1368828432015956089206328450621521371919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-36470881891330445699323727232058216000000000000)
      constant := (216527448457573322132251631401294727922707101889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234291576740863266811/100000000000000000000)
  centralHi := (58572894185215816703/25000000000000000000)
  directionLo := (119778606728753181527/50000000000000000000)
  directionHi := (47911442691501272611/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree024.table
  base := (-1040832028046841930006977957918988277591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-775748288537073013628468826968804000000000000)
      constant := (4774210292392034946897873762572217346093095058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree024.table
  base := (-2088192891292791045840174422240605327239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-38053094350200587489936256284574596000000000000)
      constant := (234442253385647858098359398875446001816342788809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119778606728753181527/50000000000000000000)
  centralHi := (47911442691501272611/20000000000000000000)
  directionLo := (244709570935283841339/100000000000000000000)
  directionHi := (12235478546764192067/5000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree025.table
  base := (-109301211671875767251296568889981433711/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-808003110646766375152754042527724000000000000)
      constant := (5158767609400614340723334017048518024851745225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree025.table
  base := (-273818786500200570325256698549865274629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-118905920427212187841646356011272928000000000000)
      constant := (759994826557463427263914939934376527360228056970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244709570935283841339/100000000000000000000)
  centralHi := (12235478546764192067/5000000000000000000)
  directionLo := (249755659986187621497/100000000000000000000)
  directionHi := (124877829993093810749/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree026.table
  base := (-3321069704922134765640876309106716885629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-840257932756459736677039258086644000000000000)
      constant := (5562869317216827659364305694362093499718839651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree026.table
  base := (-83149195397478936950516989441623928257/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-41217519267940871071161314389607356000000000000)
      constant := (273180201667799525428926506576578609372019726680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249755659986187621497/100000000000000000000)
  centralHi := (124877829993093810749/50000000000000000000)
  directionLo := (254701796779963071789/100000000000000000000)
  directionHi := (25470179677996307179/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree027.table
  base := (-154128108745635233809676237253199490723/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-872512754866153098201324473645564000000000000)
      constant := (5986256805836121693205132657134262826143215925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree027.table
  base := (-192871991806933106650156913322781523629/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-42799731726811012861773843442123736000000000000)
      constant := (293975388474655552409290024052873835661034417980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254701796779963071789/100000000000000000000)
  centralHi := (25470179677996307179/10000000000000000000)
  directionLo := (129776847772192260769/50000000000000000000)
  directionHi := (259553695544384521539/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree028.table
  base := (-2166911690064892838003766343486674675267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-904767576975846459725609689204484000000000000)
      constant := (6428716298383773051373884730492429127019324346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree028.table
  base := (-173499439558527751511169915730437167703/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-2717261888919254366472635050692252000000000000)
      constant := (19328982848340932502025246649976504055817394275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129776847772192260769/50000000000000000000)
  centralHi := (259553695544384521539/100000000000000000000)
  directionLo := (264316545941703202811/100000000000000000000)
  directionHi := (66079136485425800703/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree029.table
  base := (-2383490532792683499522814887627133766611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-937022399085539821249894904763404000000000000)
      constant := (6890070914058141642421228905221574339881329818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree029.table
  base := (-477014493894838318751171717350160766679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-45964156644551296442998901547156496000000000000)
      constant := (338365551580079482597900358576289396499840354490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264316545941703202811/100000000000000000000)
  centralHi := (66079136485425800703/25000000000000000000)
  directionLo := (4203048095438340089/1562500000000000000)
  directionHi := (268995078108053765697/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree030.table
  base := (-1031205844907308954037445443476717817511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-969277221195233182774180120322324000000000000)
      constant := (7370174170830354713756509958965187445066510045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree030.table
  base := (-644845076030034921018846376973386456239/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-47546369103421438233611430599672876000000000000)
      constant := (361944726418888490774726266995477878432369502472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4203048095438340089/1562500000000000000)
  centralHi := (268995078108053765697/100000000000000000000)
  directionLo := (136796808839025364797/50000000000000000000)
  directionHi := (54718723535610145919/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree031.table
  base := (-5503747330601825562416482673017974845263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1001532043304926544298465335881244000000000000)
      constant := (7868904658513282279765206900991805840784066897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree031.table
  base := (-5506104032113780903061208871372458046701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-147385744686874740072671878956567768000000000000)
      constant := (1159314940003985868036947534311494903029121881993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136796808839025364797/50000000000000000000)
  centralHi := (54718723535610145919/20000000000000000000)
  directionLo := (69529033154309376209/25000000000000000000)
  directionHi := (278116132617237504837/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree032.table
  base := (-290622049835557475483789635806116676573/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1033786865414619905822750551440164000000000000)
      constant := (8386161665628531625456581906554068349012295740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree032.table
  base := (-2907236688380471931681732989315739785131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-50710794021161721814836488704705636000000000000)
      constant := (411841393403725553449781117050627830703677893322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69529033154309376209/25000000000000000000)
  centralHi := (278116132617237504837/100000000000000000000)
  directionLo := (282566273305527893719/100000000000000000000)
  directionHi := (7064156832638197343/2500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree033.table
  base := (-1521006065276302924083839989941591134679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-8810261880366225349975502206604000000000000)
      constant := (73734393265055462387192232688516342401523524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree033.table
  base := (-608577612921924240304279128425635640731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-432173607272990608309496014522496000000000000)
      constant := (3621073420660796459253147359777552311511093410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282566273305527893719/100000000000000000000)
  centralHi := (7064156832638197343/2500000000000000000)
  directionLo := (143473703511810598943/50000000000000000000)
  directionHi := (286947407023621197887/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree034.table
  base := (-3160043646348443095869045314163907307503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1098296509634006628871320982558004000000000000)
      constant := (9475934956674536997723274160473988729801922914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree034.table
  base := (-6321596710507741888314642689632794672643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-161625656816706016188184640429215188000000000000)
      constant := (1396081180733166763359131315414805826697929324199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143473703511810598943/50000000000000000000)
  centralHi := (286947407023621197887/100000000000000000000)
  directionLo := (227548943569499891/78125000000000000)
  directionHi := (291262647768959860481/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree035.table
  base := (-3260976078279160155479729951197483465847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1130551331743699990395606198116924000000000000)
      constant := (10048324031312593305205812090681325449456674386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree035.table
  base := (-3261626077163900391088261619022498737719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1131784314240247901768858691066424000000000000)
      constant := (10070818438753405289549641597447571465275392722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227548943569499891/78125000000000000)
  centralHi := (291262647768959860481/100000000000000000000)
  directionLo := (36939360268974657931/12500000000000000000)
  directionHi := (295514882151797263449/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree036.table
  base := (-6690718790299385747557368910482438120407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1162806153853393351919891413675844000000000000)
      constant := (10638980762611143065851571266737840620462501833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree036.table
  base := (-6691838003009551404740720175757641523467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-57039643856642288977286604914771156000000000000)
      constant := (522476668798698582790430413802070728570058460677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36939360268974657931/12500000000000000000)
  centralHi := (295514882151797263449/100000000000000000000)
  directionLo := (299706791983425145797/100000000000000000000)
  directionHi := (149853395991712572899/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree037.table
  base := (-54618423565945143135322848500225391129/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1195060975963086713444176629234764000000000000)
      constant := (11247865149614803178748208347359034836261768875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree037.table
  base := (-1707066543882251557940888284871381426049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-175865568946537292303697401901862608000000000000)
      constant := (1657134412901881969241446860845516515502107135028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299706791983425145797/100000000000000000000)
  centralHi := (149853395991712572899/50000000000000000000)
  directionLo := (37980109257347110921/12500000000000000000)
  directionHi := (303840874058776887369/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree038.table
  base := (-173311688222545869960990779858346698779/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-3399766753664210733984658849844000000000000)
      constant := (32894581351318705969629378616917601977909640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree038.table
  base := (-277331849626693514016339869674121958919/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4197331993511521453787960209140000000000000)
      linear := (-166770273613248123430780229971756000000000000)
      constant := (1615437352485403020689400439670601272639231225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37980109257347110921/12500000000000000000)
  centralHi := (303840874058776887369/100000000000000000000)
  directionLo := (7697986438698067267/2500000000000000000)
  directionHi := (307919457547922690681/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree039.table
  base := (-7006848510148274876323498634577338857753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1259570620182473436492747060352604000000000000)
      constant := (12520189137423037232188590540401523261354491207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree039.table
  base := (-1401512253407238233274002164360811389181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-61786281233252714349124192072320296000000000000)
      constant := (614859553638076847160447883808794991438750261055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7697986438698067267/2500000000000000000)
  centralHi := (307919457547922690681/100000000000000000000)
  directionLo := (77986179835120630537/25000000000000000000)
  directionHi := (311944719340482522149/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree040.table
  base := (-3525488182013469694075396079201762095601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1291825442292166798017032275911524000000000000)
      constant := (13183577786747179042579438483309735659804105438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree040.table
  base := (-7051589209087534644408615425538271026973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-190105481076368568419210163374510028000000000000)
      constant := (1942311047367471963592762758042594549140806480889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77986179835120630537/25000000000000000000)
  centralHi := (311944719340482522149/100000000000000000000)
  directionLo := (39489837203746535761/12500000000000000000)
  directionHi := (315918697629972286089/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree041.table
  base := (-883161728132508349263110068278894861491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1324080264401860159541317491470444000000000000)
      constant := (13865090476711812388029479777734420748441693032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree041.table
  base := (-7065820615044624073271317231752372341629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-64950706150992997930349250177353056000000000000)
      constant := (680904327764711850810988023399421297563519878899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39489837203746535761/12500000000000000000)
  centralHi := (315918697629972286089/100000000000000000000)
  directionLo := (319843303978719090761/100000000000000000000)
  directionHi := (159921651989359545381/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree042.table
  base := (-440635662794645725420730440204586031989/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1356335086511553521065602707029364000000000000)
      constant := (14564711057950361459156195950401423640587015856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree042.table
  base := (-7050623301452476608649258638080497870217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1357814665507411014713505698568764000000000000)
      constant := (14597157189828771309717136759224133772531051223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319843303978719090761/100000000000000000000)
  centralHi := (159921651989359545381/50000000000000000000)
  directionLo := (323720334066040327533/100000000000000000000)
  directionHi := (161860167033020163767/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree043.table
  base := (-140118311987885301165035216633812948271/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1388589908621246882589887922588284000000000000)
      constant := (15282426037558979927204961192484792830328722450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree043.table
  base := (-700630452372966168722668831257119006059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-204345393206199844534722924847157448000000000000)
      constant := (2251516445279634489739248572353498692503615126870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323720334066040327533/100000000000000000000)
  centralHi := (161860167033020163767/50000000000000000000)
  directionLo := (81887869322794919467/25000000000000000000)
  directionHi := (327551477291179677869/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree044.table
  base := (-6932787025069800066383505501728170921933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-11742518435792894579455976348324000000000000)
      constant := (132382017656246984730553040634372130297182187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree044.table
  base := (-6933121077848561572998601828991321425851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-576011103533912589274271382933076000000000000)
      constant := (6501141458689077241056304028642516515298121661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81887869322794919467/25000000000000000000)
  centralHi := (327551477291179677869/100000000000000000000)
  directionLo := (331338325376705618769/100000000000000000000)
  directionHi := (33133832537670561877/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree045.table
  base := (-853875104625759030293015783943733826621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1453099552840633605638458353706124000000000000)
      constant := (16772095921349140746098487382089510101754944792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree045.table
  base := (-6831287691150175529464977984980836939119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-71279555986473565092799366387418576000000000000)
      constant := (823658146930366215687711305126591546021454805089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331338325376705618769/100000000000000000000)
  centralHi := (33133832537670561877/10000000000000000000)
  directionLo := (67016476019332764987/20000000000000000000)
  directionHi := (41885297512082978117/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree046.table
  base := (-6700737729869135049055696173517620413143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1485354374950326967162743569265044000000000000)
      constant := (17544033499465038826995770516349640822733500617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree046.table
  base := (-6700983997131942174976994864192315192197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-218585305336031120650235686319804868000000000000)
      constant := (2584695565694617477823970153249933963573177497921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67016476019332764987/20000000000000000000)
  centralHi := (41885297512082978117/12500000000000000000)
  directionLo := (169392530117956009789/50000000000000000000)
  directionHi := (338785060235912019579/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree047.table
  base := (-654214896165777372520329904916485784559/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1517609197060020328687028784823964000000000000)
      constant := (18334030263652934457077764172257397844446783210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree047.table
  base := (-6542360337255351102673081492447807599741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-74443980904213848674024424492451336000000000000)
      constant := (900358919618693589909672919140334105495549955571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169392530117956009789/50000000000000000000)
  centralHi := (338785060235912019579/100000000000000000000)
  directionLo := (342447707872101228777/100000000000000000000)
  directionHi := (171223853936050614389/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree048.table
  base := (-254214448094807403754779740124351043333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1549864019169713690211314000382884000000000000)
      constant := (19142080680840636400915399107404497551904280675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree048.table
  base := (-1588885647578170043481535554871748573567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-76026193363083990464636953544967716000000000000)
      constant := (940039070664764758618891047387511929509371895108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342447707872101228777/100000000000000000000)
  centralHi := (171223853936050614389/50000000000000000000)
  directionLo := (346071594059179362051/100000000000000000000)
  directionHi := (86517898514794840513/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree049.table
  base := (-3070240286678816669583344782345957650531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1582118841279407051735599215941804000000000000)
      constant := (19968180115541400087682461139299228447734310778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree049.table
  base := (-6140636194969887035348156549982766842991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-4751535050323722382974458118213312000000000000)
      constant := (60037066287271468263276930603943321284593930387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346071594059179362051/100000000000000000000)
  centralHi := (86517898514794840513/25000000000000000000)
  directionLo := (21853620248791416881/6250000000000000000)
  directionHi := (349657923980662670097/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree050.table
  base := (-2948798007282379577025128428473213775307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1614373663389100413259884431500724000000000000)
      constant := (20812324682769503667269966767437923098161629866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree050.table
  base := (-5897729502383734045050158052724394345869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-79190618280824274045862011650000476000000000000)
      constant := (1022057766596624210661901621762425140798326714339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21853620248791416881/6250000000000000000)
  centralHi := (349657923980662670097/100000000000000000000)
  directionLo := (353207841631909867149/100000000000000000000)
  directionHi := (7064156832638197343/2000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree051.table
  base := (-1406695523295987332312446904326032000971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1646628485498793774784169647059644000000000000)
      constant := (21674511125355416492272056673297322384662342996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree051.table
  base := (-5626896572150787042329209639598364158263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-80772830739694415836474540702516856000000000000)
      constant := (1064395963863470803675135897833913039904942780953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353207841631909867149/100000000000000000000)
  centralHi := (7064156832638197343/2000000000000000000)
  directionLo := (71344486816593689081/20000000000000000000)
  directionHi := (178361217041484222703/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree052.table
  base := (-2664050673871442520789889559257899333661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1678883307608487136308454862618564000000000000)
      constant := (22554736711553710921204296801506399398412707718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree052.table
  base := (-2664099752683677000990545653038965502469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-247065129595693672881261209265099708000000000000)
      constant := (3322859624720137071208561077737220550678675573634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71344486816593689081/20000000000000000000)
  centralHi := (178361217041484222703/50000000000000000000)
  directionLo := (360202735367019685283/100000000000000000000)
  directionHi := (90050683841754921321/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree053.table
  base := (-5001606245552567006943405964576459808353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1711138129718180497832740078177484000000000000)
      constant := (23452999149539775131795320582188047659111332607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree053.table
  base := (-1000338078502993607355092487335799322061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-83937255657434699417699598807549616000000000000)
      constant := (1151729388233497002298009322910729655704198097455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360202735367019685283/100000000000000000000)
  centralHi := (90050683841754921321/25000000000000000000)
  directionLo := (363649730033845426521/100000000000000000000)
  directionHi := (181824865016922713261/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree054.table
  base := (-580917602269655271922648070990160845883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1743392951827873859357025293736404000000000000)
      constant := (24369296515971724873020408217930686272727877416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree054.table
  base := (-4647412940625066940036343180590335193747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-85519468116304841208312127860065996000000000000)
      constant := (1196724410294649567882343649146182428851694927357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363649730033845426521/100000000000000000000)
  centralHi := (181824865016922713261/50000000000000000000)
  directionLo := (45883044550365720251/12500000000000000000)
  directionHi := (367064356402925762009/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree055.table
  base := (-1066335507112145714189062882585632620939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-14674774991219563808936450490044000000000000)
      constant := (209120885919615611625722545775466346495364084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree055.table
  base := (-2132701916609978316525702907602702338557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530670000000000000000000000000000000000000000
      center := (7747782)
      previous := (3873891)
      next := (3873891)
      square := (37567855776636179623573230632220000000000000)
      linear := (-2159545799384503710717140254030968000000000000)
      constant := (30808385022493291721159076796547259789999591362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45883044550365720251/12500000000000000000)
  centralHi := (367064356402925762009/100000000000000000000)
  directionLo := (370447509546628688467/100000000000000000000)
  directionHi := (92611877386657172117/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree056.table
  base := (-1927820457012844668771630700858100270779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1807902596047260582405595724854244000000000000)
      constant := (26255989834691701233257880659497138644144205002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree056.table
  base := (-963923466866639298430394806625981077997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1809875368041737240602799713573444000000000000)
      constant := (26313687329672147619408366012156026082128052172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370447509546628688467/100000000000000000000)
  centralHi := (92611877386657172117/25000000000000000000)
  directionLo := (186900022015183962701/50000000000000000000)
  directionHi := (373800044030367925403/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree057.table
  base := (-1709131771932668682446883060334890573259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-5097388969963861340525985984524000000000000)
      constant := (75419344300574479255527532242926956481271322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree057.table
  base := (-3418308905480290907577065413053275806787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4197331993511521453787960209140000000000000)
      linear := (-250044613553781901884071232735776000000000000)
      constant := (3703661508809686552335920131937474127741559877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186900022015183962701/50000000000000000000)
  centralHi := (373800044030367925403/100000000000000000000)
  directionLo := (75424555286699687939/20000000000000000000)
  directionHi := (23570173527093652481/6250000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree058.table
  base := (-369153977392365742703202667097003281339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1872412240266647305454166155972084000000000000)
      constant := (28214806613055478460833016726800918397342649128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree058.table
  base := (-1476635335252248226009792505753123175993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-275544953855356225112286732210394548000000000000)
      constant := (4156674577971672941955728459494208705005538231498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75424555286699687939/20000000000000000000)
  centralHi := (23570173527093652481/6250000000000000000)
  directionLo := (380416487672019668667/100000000000000000000)
  directionHi := (95104121918004917167/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree059.table
  base := (-2460564143848509135138202534616172587429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1904667062376340666978451371531004000000000000)
      constant := (29221258992430761858302541300268006965208513851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree059.table
  base := (-123029870677041180655788523594375639509/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-93430530410655550161374773122647896000000000000)
      constant := (1434979804020839488975983239171142635136795223580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380416487672019668667/100000000000000000000)
  centralHi := (95104121918004917167/25000000000000000000)
  directionLo := (383681925141804587163/100000000000000000000)
  directionHi := (95920481285451146791/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree060.table
  base := (-388055197333799450456502463763873212637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1936921884486034028502736587089924000000000000)
      constant := (30245739754946048446540454215325091270994016015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree060.table
  base := (-970152235866615324852394157537953467287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-95012742869525691951987302175164276000000000000)
      constant := (1485286605943994893570975097641520456150352782194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383681925141804587163/100000000000000000000)
  centralHi := (95920481285451146791/25000000000000000000)
  directionLo := (48364975587377339457/12500000000000000000)
  directionHi := (386919804699018715657/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree061.table
  base := (-1392380351824824528113282469019276104089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-1969176706595727390027021802648844000000000000)
      constant := (31288248332563810713725329733105993000497288391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree061.table
  base := (-696202368130188115775362354616414923613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-289784865985187501227799493683041968000000000000)
      constant := (4609435712504434059875622323684624744638168200818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48364975587377339457/12500000000000000000)
  centralHi := (386919804699018715657/100000000000000000000)
  directionLo := (3121046499940759107/800000000000000000)
  directionHi := (48766351561574361047/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree062.table
  base := (-204222043467935895484298288076326061083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2001431528705420751551307018207764000000000000)
      constant := (32348784247651718829693232757232080005303333908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree062.table
  base := (-816909044543170339721226488486111665827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-98177167787265975533212360280197036000000000000)
      constant := (1588555675497209112463412491744490661659925529837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3121046499940759107/800000000000000000)
  centralHi := (48766351561574361047/12500000000000000000)
  directionLo := (78663121332410317277/20000000000000000000)
  directionHi := (196657803331025793193/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree063.table
  base := (-106904324397307304551698919540293439471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2033686350815114113075592233766684000000000000)
      constant := (33427347098519958116251116914962672884540934498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree063.table
  base := (-213826509122865553032100344762643511899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2035905719308900353547446721075784000000000000)
      constant := (33500365314836476792749445710958669968756739781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78663121332410317277/20000000000000000000)
  centralHi := (196657803331025793193/50000000000000000000)
  directionLo := (396474818912554804217/100000000000000000000)
  directionHi := (198237409456277402109/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree064.table
  base := (416850488215103942831292146863657306819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2065941172924807474599877449325604000000000000)
      constant := (34523936547287630476951253130863247414819160739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree064.table
  base := (104208801618686265052034300942957299717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-304024778115018777343312255155689388000000000000)
      constant := (5086095687664119198755948162942572550871655706876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396474818912554804217/100000000000000000000)
  centralHi := (198237409456277402109/50000000000000000000)
  directionLo := (99902263994475048599/25000000000000000000)
  directionHi := (399609055977900194397/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree065.table
  base := (1075082729643340443815106237658326906963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2098195995034500836124162664884524000000000000)
      constant := (35638552309700013748921350014758713377623050803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree065.table
  base := (215013931254386803810369391185052499267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-102923805163876400905049947437746176000000000000)
      constant := (1750097648083595320094523717606722513164018047615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/25000000000000000000)
  centralHi := (399609055977900194397/100000000000000000000)
  directionLo := (402718900981011837973/100000000000000000000)
  directionHi := (201359450490505918987/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree066.table
  base := (88044129998039625857229370696536065551/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-17607031546646233038416924631764000000000000)
      constant := (303894166500665392355740693062692990393278220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree066.table
  base := (14086971340532189609628006583494641597/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-863686096055756551203822119754236000000000000)
      constant := (14923265664521243695513146880617825589401166625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402718900981011837973/100000000000000000000)
  centralHi := (201359450490505918987/50000000000000000000)
  directionLo := (405804914700597809229/100000000000000000000)
  directionHi := (40580491470059780923/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree067.table
  base := (494849098260063643506109575304590509253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2162705639253887559172733096002364000000000000)
      constant := (37921861856652882028008897656089647090173401465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree067.table
  base := (247423592783215771629063985376372013951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-318264690244850053458825016628336808000000000000)
      constant := (5586653134278925777616336328697128340733848637570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405804914700597809229/100000000000000000000)
  centralHi := (40580491470059780923/10000000000000000000)
  directionLo := (10221690918793869937/2500000000000000000)
  directionHi := (408867636751754797481/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree068.table
  base := (401895940679923385735715102618535742963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2194960461363580920697018311561284000000000000)
      constant := (39090555270512484054830780499983314078306934424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree068.table
  base := (3215159347753488749415809490937572859343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-107670442540486826276887534595295316000000000000)
      constant := (1919605337923758085622547978725866169883379117567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10221690918793869937/2500000000000000000)
  centralHi := (408867636751754797481/100000000000000000000)
  directionLo := (411907586687560729107/100000000000000000000)
  directionHi := (102976896671890182277/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree069.table
  base := (3983645437847809742392976904628955063061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2227215283473274282221303527120204000000000000)
      constant := (40277274245561375353210480365453713386109567541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree069.table
  base := (1991819223089958221963690272534604523243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-109252654999356968067500063647811696000000000000)
      constant := (1977878017983564387073632289118763336897618193334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411907586687560729107/100000000000000000000)
  centralHi := (102976896671890182277/25000000000000000000)
  directionLo := (103731316257005953893/25000000000000000000)
  directionHi := (414925265028023815573/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree070.table
  base := (4779676480250203969697950228332829695643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2259470105582967643745588742679124000000000000)
      constant := (41482018661752138952511741195656486333935381883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree070.table
  base := (4779670503467570242449489671019398253523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-6785808211728190399476281185734372000000000000)
      constant := (124716474231715473386388470703605835005336414489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103731316257005953893/25000000000000000000)
  centralHi := (414925265028023815573/100000000000000000000)
  directionLo := (417921154222158572021/100000000000000000000)
  directionHi := (208960577111079286011/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree071.table
  base := (560325833872865687173909858380584384177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2291724927692661005269873958238044000000000000)
      constant := (42704788418010526499521698765392887064852355370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree071.table
  base := (56032532302524789548263891122577179149/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-112417079917097251648725121752844456000000000000)
      constant := (2097078516427039446682383708176364810435796598100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417921154222158572021/100000000000000000000)
  centralHi := (208960577111079286011/50000000000000000000)
  directionLo := (10522392988710632881/2500000000000000000)
  directionHi := (420895719548425315241/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree072.table
  base := (3227194532436325087853119317079680145689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2323979749802354366794159173796964000000000000)
      constant := (43945583429228018145565731456324283016887682418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree072.table
  base := (20169952184928406127230910903241503289/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-113999292375967393439337650805360836000000000000)
      constant := (2158006325785368173643294881173370388209015565120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10522392988710632881/2500000000000000000)
  centralHi := (420895719548425315241/100000000000000000000)
  directionLo := (423849409958291840579/100000000000000000000)
  directionHi := (21192470497914592029/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree073.table
  base := (733306701788618935664516802818466153711/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2356234571912047728318444389355884000000000000)
      constant := (45204403623733004053799314755547526200602501910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree073.table
  base := (7333063287493108669306920877354930716039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-346744514504512605689850539573631648000000000000)
      constant := (6659457511159176304946155012798587976105273035173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423849409958291840579/100000000000000000000)
  centralHi := (21192470497914592029/5000000000000000000)
  directionLo := (426782658867247778549/100000000000000000000)
  directionHi := (8535653177344955571/2000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree074.table
  base := (329571632635969645175982352807604001167/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2388489394021741089842729604914804000000000000)
      constant := (46481248941164019300293535102066859759374393175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree074.table
  base := (8239287628799005255181439263418935656003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-117163717293707677020562708910393596000000000000)
      constant := (2282517047305507754707741054635300227891103485107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426782658867247778549/100000000000000000000)
  centralHi := (8535653177344955571/2000000000000000000)
  directionLo := (429695884897217784983/100000000000000000000)
  directionHi := (53711985612152223123/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree075.table
  base := (4586529647506438590251908108041100794801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2420744216131434451367014820473724000000000000)
      constant := (47776119330680794797387901849681486647635404962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree075.table
  base := (9173056572451283257467903368522009209513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-118745929752577818811175237962909976000000000000)
      constant := (2346099954079913462943908148802779659329756130297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429695884897217784983/100000000000000000000)
  centralHi := (53711985612152223123/12500000000000000000)
  directionLo := (108147373143493550641/25000000000000000000)
  directionHi := (86517898514794840513/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree076.table
  base := (10134371474843971650276252697060323360729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-6795011186263511947067313119204000000000000)
      constant := (135980650275510291480348086442888299126648209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree076.table
  base := (5067184574711859087420669994767026836227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 177870000000000000000000000000000000000000000
      center := (2596902)
      previous := (1298451)
      next := (1298451)
      square := (12591995980534564361363880627420000000000000)
      linear := (-999956860482947041012086706499388000000000000)
      constant := (20032420127165115251364624835447290212671939298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108147373143493550641/25000000000000000000)
  centralHi := (86517898514794840513/20000000000000000000)
  directionLo := (54432984122854844891/12500000000000000000)
  directionHi := (435463872982838759129/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree077.table
  base := (11123226529533428164313274040891344671337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-20539288102072902267897398773484000000000000)
      constant := (416693679020040738781954411334289775426352657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree077.table
  base := (5561612271792874064916257302746735530527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-20561705965646500656501989554384000000000000)
      constant := (417595015892317999160655966571266143053040494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54432984122854844891/12500000000000000000)
  centralHi := (435463872982838759129/100000000000000000000)
  directionLo := (219159702192841199453/50000000000000000000)
  directionHi := (438319404385682398907/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree078.table
  base := (12139623763347991611760347642446587356263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2517508682460514535939870467150484000000000000)
      constant := (51768880536187612985523138707656021382308924103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree078.table
  base := (12139622067536281165322921034314693707081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-123492567129188244183012825120459116000000000000)
      constant := (2542158834378675120480700480650974474655131252889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219159702192841199453/50000000000000000000)
  centralHi := (438319404385682398907/100000000000000000000)
  directionLo := (110289113200494777183/25000000000000000000)
  directionHi := (441156452801979108733/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree079.table
  base := (3295890647536240930488644162722208534779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2549763504570207897464155682709404000000000000)
      constant := (53135850848143966799964798017162131164030725996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree079.table
  base := (3295890285566896746464773796489860025977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-375224338764175157920876062518926488000000000000)
      constant := (7827845528566831346802922552803115939567284386156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110289113200494777183/25000000000000000000)
  centralHi := (441156452801979108733/100000000000000000000)
  directionLo := (443975372556440643209/100000000000000000000)
  directionHi := (44397537255644064321/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree080.table
  base := (14255042516085958657937907404803083094173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2582018326679901258988440898268324000000000000)
      constant := (54520846075722636304197296957983123472636570813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree080.table
  base := (570201651202000618489803241537982793567/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-126656992046928527764237883225491876000000000000)
      constant := (2677289873612437978866973317456424147347105155575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443975372556440643209/100000000000000000000)
  centralHi := (44397537255644064321/10000000000000000000)
  directionLo := (22338825339777588329/5000000000000000000)
  directionHi := (446776506795551766581/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree081.table
  base := (3838515781270963619769965410508735348799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2614273148789594620512726113827244000000000000)
      constant := (55923866200748519924731955609149832275083556476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree081.table
  base := (7677031035012831597806946970742364172329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-128239204505798669554850412278008256000000000000)
      constant := (2746182925769770190438768351148152257522327298802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/5000000000000000000)
  centralHi := (446776506795551766581/100000000000000000000)
  directionLo := (89912037595027543739/20000000000000000000)
  directionHi := (56195023496892214837/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree082.table
  base := (16480624066549368023501227490589220270973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2646527970899287982037011329386164000000000000)
      constant := (57344911207907527183774728116881635730656371613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree082.table
  base := (3296124633216165731926757847421004446843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-389464250894006434036388823991573908000000000000)
      constant := (8447882995760388139282438406083230054003273576005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89912037595027543739/20000000000000000000)
  centralHi := (56195023496892214837/12500000000000000000)
  directionLo := (9046534766418501013/2000000000000000000)
  directionHi := (452326738320925050651/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree083.table
  base := (17634725045072754340630501190197793028649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2678782793008981343561296544945084000000000000)
      constant := (58783981084295865012139700625426261797284416969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree083.table
  base := (3526944855327138747809880991711635455621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-131403629423538953136075470383041016000000000000)
      constant := (2886624091439427143113575666257781830342560320745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9046534766418501013/2000000000000000000)
  centralHi := (452326738320925050651/100000000000000000000)
  directionLo := (113769117565975492279/25000000000000000000)
  directionHi := (455076470263901969117/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree084.table
  base := (9408182905867070109578825899865155567131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2711037615118674705085581760504004000000000000)
      constant := (60241075819040464428083639673244195720655698422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree084.table
  base := (4704091289011816857878736457407531561583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2713996773110389692381387743582804000000000000)
      constant := (60370861302079527295680756660177809544566028092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113769117565975492279/25000000000000000000)
  centralHi := (455076470263901969117/100000000000000000000)
  directionLo := (457809686852143288673/100000000000000000000)
  directionHi := (228904843426071644337/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree085.table
  base := (2503193269598091207225220733538076733447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2743292437228368066609866976062924000000000000)
      constant := (61716195402979288273474593679887453838349587256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree085.table
  base := (20025545597370002140512574639262771931113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-403704163023837710151901585464221328000000000000)
      constant := (9091816005693795884364637236760821964686273202091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457809686852143288673/100000000000000000000)
  centralHi := (228904843426071644337/50000000000000000000)
  directionLo := (9210533642812732183/2000000000000000000)
  directionHi := (460526682140636609151/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree086.table
  base := (2657783237935257732041968213575975474941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2775547259338061428134152191621844000000000000)
      constant := (63209339828392049118097842791276521477767182568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree086.table
  base := (4252453085251826224334343139012269311251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-136150266800149378507913057540590156000000000000)
      constant := (3103923485354370380961259969248310495267264958095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9210533642812732183/2000000000000000000)
  centralHi := (460526682140636609151/100000000000000000000)
  directionLo := (18529109662421166313/4000000000000000000)
  directionHi := (231613870780264578913/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree087.table
  base := (2815815612862113910752285059536434609251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2807802081447754789658437407180764000000000000)
      constant := (64720509088773369461632437808419416001333543448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree087.table
  base := (11263262247917961174047993601136971660993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-137732479259019520298525586593106536000000000000)
      constant := (3178126653856837411217823565527170844794135852834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18529109662421166313/4000000000000000000)
  centralHi := (231613870780264578913/50000000000000000000)
  directionLo := (1455978569590961719/312500000000000000)
  directionHi := (465913142269107750081/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree088.table
  base := (11909161514769171783533153247055851246807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-23471544657499571497377872915204000000000000)
      constant := (547518208087947766937479956420086324600194654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree088.table
  base := (5954580670590685612454674682138710138981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530670000000000000000000000000000000000000000
      center := (7747782)
      previous := (3873891)
      next := (3873891)
      square := (37567855776636179623573230632220000000000000)
      linear := (-3454083265732801539400118569726188000000000000)
      constant := (80658219185301376635358536343542123723781218908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1455978569590961719/312500000000000000)
  centralHi := (465913142269107750081/100000000000000000000)
  directionLo := (234291576740863266811/50000000000000000000)
  directionHi := (468583153481726533623/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree089.table
  base := (25137660177667759492586414249997927487663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2872311725667141512707007838298604000000000000)
      constant := (67796922093378212379549442525612855470588607503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree089.table
  base := (25137659881599948686938425056824083441197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-140896904176759803879750644698139296000000000000)
      constant := (3329188044982213420294612096644938725650951381693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234291576740863266811/50000000000000000000)
  centralHi := (468583153481726533623/100000000000000000000)
  directionLo := (235619018393403852407/50000000000000000000)
  directionHi := (94247607357361540963/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree090.table
  base := (26484536258193209879649478825735588335791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2904566547776834874231293053857524000000000000)
      constant := (69362165829091341769716014099214116234095686671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree090.table
  base := (2648453600573691007796237082044458587531/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-142479116635629945670363173750655676000000000000)
      constant := (3406046267194063946800050204967296397825351389390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235619018393403852407/50000000000000000000)
  centralHi := (94247607357361540963/20000000000000000000)
  directionLo := (118469511611239607283/25000000000000000000)
  directionHi := (473878046444958429133/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree091.table
  base := (5571790239210492889141650148764502898419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2936821369886528235755578269416444000000000000)
      constant := (70945434382502274688962843043207455255529201695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree091.table
  base := (27858950980806515520174310143646697982209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-8820081373132658415978104253255432000000000000)
      constant := (213293235119452460746038714193578171243682613987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118469511611239607283/25000000000000000000)
  centralHi := (473878046444958429133/100000000000000000000)
  directionLo := (476503429673172052939/100000000000000000000)
  directionHi := (23825171483658602647/5000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree092.table
  base := (1828806558000486720624716774485193676767/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-2969076191996221597279863484975364000000000000)
      constant := (72546727750848723605891954603097451919917749232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree092.table
  base := (29260904744506872696975450720344876950793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-145643541553370229251588231855688436000000000000)
      constant := (3562417764119843117494572236738995915934291862617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476503429673172052939/100000000000000000000)
  centralHi := (23825171483658602647/5000000000000000000)
  directionLo := (119778606728753181527/25000000000000000000)
  directionHi := (479114426915012726109/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree093.table
  base := (30690397400787547759336572437406455489867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3001331014105914958804148700534284000000000000)
      constant := (74166045931803730390491710852696423382252880427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree093.table
  base := (7672599311091492382024806469821848616667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-147225754012240371042200760908204816000000000000)
      constant := (3641931038588113254703641848659373364207227720492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119778606728753181527/25000000000000000000)
  centralHi := (479114426915012726109/100000000000000000000)
  directionLo := (481711272097619195171/100000000000000000000)
  directionHi := (120427818024404798793/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree094.table
  base := (8036857142380008344218182632350683652237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3033585836215608320328433916093204000000000000)
      constant := (75803388923407253801510761136065056850453457588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree094.table
  base := (16073714218097611576250882356604246942207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-446423899413331538498439869882163588000000000000)
      constant := (11166987990783862192708394675978986924540667926298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481711272097619195171/100000000000000000000)
  centralHi := (120427818024404798793/25000000000000000000)
  directionLo := (96858838575261052691/20000000000000000000)
  directionHi := (15134193527384539483/3125000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree095.table
  base := (33631998396413467010491113995804906512669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-8492633402563162553608640253884000000000000)
      constant := (214567193141297814990464944553972393688032949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree095.table
  base := (840799957069659624035683890111928092683/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4197331993511521453787960209140000000000000)
      linear := (-416593293434849458790653238263816000000000000)
      constant := (10536323099888438128048663470971039866460700280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96858838575261052691/20000000000000000000)
  centralHi := (15134193527384539483/3125000000000000000)
  directionLo := (243431705433740394179/50000000000000000000)
  directionHi := (486863410867480788359/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree096.table
  base := (17572053424821735562481622134405018726581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3098095480434995043377004347211044000000000000)
      constant := (79132149332217381985516647224133155245991569322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree096.table
  base := (17572053376406730098876872668836300988251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-151972391388850796414038348065753956000000000000)
      constant := (3885780964916380366599642711749585865419843609238) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243431705433740394179/50000000000000000000)
  centralHi := (486863410867480788359/100000000000000000000)
  directionLo := (244709570935283841339/50000000000000000000)
  directionHi := (489419141870567682679/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree097.table
  base := (9170938475603836257440843069452476841997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3130350302544688404901289562769964000000000000)
      constant := (80823566746863446802524312611359182563741083828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree097.table
  base := (7336750763981470462815970970342214779059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-460663811543162814613952631354811008000000000000)
      constant := (11906502923324431223650878563973672219566595991565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244709570935283841339/50000000000000000000)
  centralHi := (489419141870567682679/100000000000000000000)
  directionLo := (245980798039769916843/50000000000000000000)
  directionHi := (491961596079539833687/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree098.table
  base := (1530037581286946330592255964427899370339/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3162605124654381766425574778328884000000000000)
      constant := (82533008966961461904653863940082368809894446475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree098.table
  base := (38250939461876036466370975509762862963487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3166057475644715918270681758587484000000000000)
      constant := (82709646277296268694981963601125663617108075647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245980798039769916843/50000000000000000000)
  centralHi := (491961596079539833687/100000000000000000000)
  directionLo := (494490978284673814009/100000000000000000000)
  directionHi := (49449097828467381401/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree099.table
  base := (9961415929983999145847726627647671042879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-26403801212926240726858347056924000000000000)
      constant := (696367570179192202109050715367139236985917276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree099.table
  base := (3984566366004735519000820101158689281063/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-1295198584838522494098148224985976000000000000)
      constant := (34195008630698639124882015646962359546927234070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494490978284673814009/100000000000000000000)
  centralHi := (49449097828467381401/10000000000000000000)
  directionLo := (248503744032529214077/50000000000000000000)
  directionHi := (99401497613011685631/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree100.table
  base := (10366981612432836084460263010318611544363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3227114768873768489474145209446724000000000000)
      constant := (86005967820328200519642001995927309083477280812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree100.table
  base := (8293585279743028043115970744719517495083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-474903723672994090729465392827458428000000000000)
      constant := (12669913313766743749142450446284504334121499584405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248503744032529214077/50000000000000000000)
  centralHi := (99401497613011685631/20000000000000000000)
  directionLo := (99902263994475048599/20000000000000000000)
  directionHi := (124877829993093810749/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree101.table
  base := (43117727708126659112307320660248600879689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3259369590983461850998430425005644000000000000)
      constant := (87769484452312525372227737583021303135025695209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree101.table
  base := (43117727664672404946019813092410615161491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-159883453683201505367100993328335856000000000000)
      constant := (4309897848382387088168619167509598666962585330179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99902263994475048599/20000000000000000000)
  centralHi := (124877829993093810749/25000000000000000000)
  directionLo := (62750332963303630081/12500000000000000000)
  directionHi := (502002663706429040649/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree102.table
  base := (2799691717739236374866197639508471550533/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3291624413093155212522715640564564000000000000)
      constant := (89551025887141890857651347960242400732781311568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree102.table
  base := (44795067446817912661833646229224295671533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-161465666142071647157713522380852236000000000000)
      constant := (4397376275671192106538063369698965608502183415677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62750332963303630081/12500000000000000000)
  centralHi := (502002663706429040649/100000000000000000000)
  directionLo := (504481704282876382663/100000000000000000000)
  directionHi := (63060213035359547833/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree103.table
  base := (2324997288367150328447204032533262259783/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3323879235202848574047000856123484000000000000)
      constant := (91350592124401689747538274545172620575391624460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree103.table
  base := (23249972867912291009478445397891960770157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-489143635802825366844978154300105848000000000000)
      constant := (13457219159306098727159506538417403138089961007598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504481704282876382663/100000000000000000000)
  centralHi := (63060213035359547833/12500000000000000000)
  directionLo := (101389724438714396103/20000000000000000000)
  directionHi := (126737155548392995129/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree104.table
  base := (24116181275349732923768024112943037402761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3356134057312541935571286071682404000000000000)
      constant := (93168183163743659239421362422287185633580006482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree104.table
  base := (12058090630965001940631299643204164251621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-164630091059811930738938580485884996000000000000)
      constant := (4574988180658145258310986846696368199340311152596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101389724438714396103/20000000000000000000)
  centralHi := (126737155548392995129/25000000000000000000)
  directionLo := (509403593559926143579/100000000000000000000)
  directionHi := (25470179677996307179/5000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree105.table
  base := (12498079456801010891576189115797832914767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3388388879422235297095571287241324000000000000)
      constant := (95003799004875437321627356386233180558199749308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree105.table
  base := (24996158902175452283997740679774062689761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3392087826911879031215328766089824000000000000)
      constant := (95206564455621630574994089922887016664702900482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509403593559926143579/100000000000000000000)
  centralHi := (25470179677996307179/5000000000000000000)
  directionLo := (127961697569910513253/25000000000000000000)
  directionHi := (511846790279642053013/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree106.table
  base := (25889905795620909754788411733288972646007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3420643701531928658619856502800244000000000000)
      constant := (96857439647551758664215427442411295228300463534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree106.table
  base := (10355962314356914156530515311749503457673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-503383547932656642960490915772753268000000000000)
      constant := (14268420458276532838761857674584046762492941520055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127961697569910513253/25000000000000000000)
  centralHi := (511846790279642053013/100000000000000000000)
  directionLo := (128569595041794708743/25000000000000000000)
  directionHi := (514278380167178834973/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree107.table
  base := (26797421919053078520658306277961672192749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3452898523641622020144141718359164000000000000)
      constant := (98729105091567032672286902944997095606102938138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree107.table
  base := (13398710955385388662932221544312808700813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-169376728436422356110776167643434136000000000000)
      constant := (4848043663948411071215813133666993935184601679988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128569595041794708743/25000000000000000000)
  centralHi := (514278380167178834973/100000000000000000000)
  directionLo := (516698527088265239319/100000000000000000000)
  directionHi := (12917463177206630983/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree108.table
  base := (55437414563855466466815912242329102457939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3485153345751315381668426933918084000000000000)
      constant := (100618795336749086766387233507944009524465233459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree108.table
  base := (55437414549754620422131281314050601099271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-170958940895292497901388696695950516000000000000)
      constant := (4940832191885882961538679945425675819024245570999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516698527088265239319/100000000000000000000)
  centralHi := (12917463177206630983/2500000000000000000)
  directionLo := (519107391088769043077/100000000000000000000)
  directionHi := (259553695544384521539/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree109.table
  base := (14326880941298114462750113659118834980203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3517408167861008743192712149477004000000000000)
      constant := (102526510382953892024862440035578655323080988972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree109.table
  base := (28653761876594941250259116203323010689317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-517623460062487919076003677245400688000000000000)
      constant := (15103517209693014726247054531547710631396496427838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519107391088769043077/100000000000000000000)
  centralHi := (259553695544384521539/50000000000000000000)
  directionLo := (104301025703641795037/20000000000000000000)
  directionHi := (260752564259104487593/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree110.table
  base := (59205171439362354261391075909158823164573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-29336057768352909956338821198644000000000000)
      constant := (863241737438521628401032232832046335162410853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree110.table
  base := (37003232143216640820539767291367635927/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-1439036081099444475062923593396556000000000000)
      constant := (42388961140314019710366654000613963379060324800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104301025703641795037/20000000000000000000)
  centralHi := (260752564259104487593/50000000000000000000)
  directionLo := (261945946074089447131/50000000000000000000)
  directionHi := (523891892148178894263/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree111.table
  base := (30565178792033545213955807000520319800369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3581917812080395466241282580594844000000000000)
      constant := (106396014877970380012312417084326880178399836578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree111.table
  base := (7641294696921609224018336130690785969147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-175705578271902923273226283853499656000000000000)
      constant := (5224507876122037332532496620412831565991977561944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261945946074089447131/50000000000000000000)
  centralHi := (523891892148178894263/100000000000000000000)
  directionLo := (8222934863842781989/1562500000000000000)
  directionHi := (526267831285938047297/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree112.table
  base := (2523323287895719551125178753377375860043/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3614172634190088827765567796153764000000000000)
      constant := (108357804326598089602183562366533056873563457075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree112.table
  base := (63083082189994240611511029960472460903269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1310430000000000000000000000000000000000000000
      center := (19132278)
      previous := (9566139)
      next := (9566139)
      square := (92769603040264851723517569520380000000000000)
      linear := (-10854354534537126432479927320776492000000000000)
      constant := (325765498224027502303368348504166416694147079567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8222934863842781989/1562500000000000000)
  centralHi := (526267831285938047297/100000000000000000000)
  directionLo := (264316545941703202811/50000000000000000000)
  directionHi := (528633091883406405623/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree113.table
  base := (65063345277749798413525510211670017273451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3646427456299782189289853011712684000000000000)
      constant := (110337618575874782056640121893131710024521613131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree113.table
  base := (65063345271453964942200105730032431229053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-178870003189643206854451341958532416000000000000)
      constant := (5418050082585899957603639532757634187797296940557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264316545941703202811/50000000000000000000)
  centralHi := (528633091883406405623/100000000000000000000)
  directionLo := (132746954160447558513/25000000000000000000)
  directionHi := (530987816641790234053/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree114.table
  base := (67071146823819314379080631948678552485933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-10190255618862813160149967388564000000000000)
      constant := (311178552979897165831141014091126104850797893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree114.table
  base := (6707114681846238506915075819909527665833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4197331993511521453787960209140000000000000)
      linear := (-499867633375383237243944241027836000000000000)
      constant := (15280190334902020056850299515856739895307238570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132746954160447558513/25000000000000000000)
  centralHi := (530987816641790234053/100000000000000000000)
  directionLo := (1333330362780125313/250000000000000000)
  directionHi := (533332145112050125201/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree115.table
  base := (172766217086280185664446201123019016761/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3710937100519168912338423442830524000000000000)
      constant := (114351321476154785219900671606389597468454896400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree115.table
  base := (34553243414977181630693737047098165933017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-546103284322150471307029200190695528000000000000)
      constant := (16845397067794071795798585423795157770919313979638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1333330362780125313/250000000000000000)
  centralHi := (533332145112050125201/100000000000000000000)
  directionLo := (267833106895705827843/50000000000000000000)
  directionHi := (535666213791411655687/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree116.table
  base := (7116936530893086496349069284832071202069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3743191922628862273862708658389444000000000000)
      constant := (116385210127071315955352901433307641021775759890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree116.table
  base := (35584682652526706985925057600400295236157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-183616640566253632226288929116081556000000000000)
      constant := (5715001017679208029339475019909836575028636243866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267833106895705827843/50000000000000000000)
  centralHi := (535666213791411655687/100000000000000000000)
  directionLo := (537990156216107531393/100000000000000000000)
  directionHi := (268995078108053765697/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree117.table
  base := (14651956449267994230138989258813388593849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3775446744738555635386993873948364000000000000)
      constant := (118437123578460332290439178983154586135839590845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree117.table
  base := (1831494556076037063940342876655387471513/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-185198853025123774016901458168597936000000000000)
      constant := (5815754696141644630844775093637251948080592331880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537990156216107531393/100000000000000000000)
  centralHi := (268995078108053765697/50000000000000000000)
  directionLo := (21612164122021181117/4000000000000000000)
  directionHi := (270152051525264763963/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree118.table
  base := (75377737646139264682164039271062403238547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3807701566848248996911279089507284000000000000)
      constant := (120507061830295620027647834866536948835862971507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree118.table
  base := (117777715067708573463952212582498376157/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-560343196451981747422541961663342948000000000000)
      constant := (17752180173952244335209282485322829000403421311360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21612164122021181117/4000000000000000000)
  centralHi := (270152051525264763963/50000000000000000000)
  directionLo := (108521636434591729381/20000000000000000000)
  directionHi := (271304091086479323453/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree119.table
  base := (3876161575392118765799632429225501890699/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3839956388957942358435564305066204000000000000)
      constant := (122595024882555934028442202660982798961752460380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree119.table
  base := (77523231505455874578857714608917545662529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3844148529446205257104622781094504000000000000)
      constant := (122855451085826630496809167551910278312084929249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108521636434591729381/20000000000000000000)
  centralHi := (271304091086479323453/50000000000000000000)
  directionLo := (272451259379016325171/50000000000000000000)
  directionHi := (544902518758032650343/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree120.table
  base := (79696263831058302336345328133615185204461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3872211211067635719959849520625124000000000000)
      constant := (124701012735224194990553874245363324904916060941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree120.table
  base := (79696263829028562436487355634297187789931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-189945490401734199388739045326147076000000000000)
      constant := (6123325831805101461209094402277515357532746824539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272451259379016325171/50000000000000000000)
  centralHi := (544902518758032650343/100000000000000000000)
  directionLo := (547187235356101459189/100000000000000000000)
  directionHi := (54718723535610145919/10000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree121.table
  base := (818968346154759270581638108611741921307/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-32268314323779579185819295340364000000000000)
      constant := (1048140705688320768088436524432667883359182700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree121.table
  base := (40948417306874865462699583346886648400461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530670000000000000000000000000000000000000000
      center := (7747782)
      previous := (3873891)
      next := (3873891)
      square := (37567855776636179623573230632220000000000000)
      linear := (-4748620732081099368083096885421408000000000000)
      constant := (154403791168154342319325203441077620541334527774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547187235356101459189/100000000000000000000)
  centralHi := (54718723535610145919/10000000000000000000)
  directionLo := (274731225984806383647/50000000000000000000)
  directionHi := (109892490393922553459/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree122.table
  base := (84124943860850970877839171679896055106991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3936720855287022443008419951742964000000000000)
      constant := (128967062841733117539198796837213307583128473871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree122.table
  base := (84124943859383020913529131749407812440191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-193109915319474482969964103431179836000000000000)
      constant := (6332798339136370035595578893638344202104799170479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274731225984806383647/50000000000000000000)
  centralHi := (109892490393922553459/20000000000000000000)
  directionLo := (551728286126662590237/100000000000000000000)
  directionHi := (275864143063331295119/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree123.table
  base := (43190295783497507465866113442388833929137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-3968975677396715804532705167301884000000000000)
      constant := (131127125095554878467665183204526565309717266594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree123.table
  base := (86380591565746757529387625141356194243373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-194692127778344624760576632483696216000000000000)
      constant := (6438862117867147296094466088238220079116494024637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551728286126662590237/100000000000000000000)
  centralHi := (275864143063331295119/50000000000000000000)
  directionLo := (5539848529518383051/1000000000000000000)
  directionHi := (553984852951838305101/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree124.table
  base := (1108297221672078220328129469895491143409/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4001230499506409166056990382860804000000000000)
      constant := (133305212149745901688690259372812731890819882320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree124.table
  base := (4433188886635244083554180657487597427893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-588823020711644299653567484608637788000000000000)
      constant := (19637432739922797115076768137913404197148514751020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5539848529518383051/1000000000000000000)
  centralHi := (553984852951838305101/100000000000000000000)
  directionLo := (69529033154309376209/12500000000000000000)
  directionHi := (556232265234475009673/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree125.table
  base := (11371812795132717133190397517475326039689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4033485321616102527581275598419724000000000000)
      constant := (135501324004301689723700511113389717733917241672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree125.table
  base := (4548725118007966037177363604280231431047/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-197856552696084908341801690588728976000000000000)
      constant := (6653644725457515350846711763377707368356772726860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69529033154309376209/12500000000000000000)
  centralHi := (556232265234475009673/100000000000000000000)
  directionLo := (22338825339777588329/4000000000000000000)
  directionHi := (279235316747219854113/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree126.table
  base := (93312765448810788206312768076429903278223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4065740143725795889105560813978644000000000000)
      constant := (137715460659219155852942262560871118605096058863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree126.table
  base := (5832047840502723264239182925808669471717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4070178880713368370049269788596844000000000000)
      constant := (138007419475852120278119329846914799859105124432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22338825339777588329/4000000000000000000)
  centralHi := (279235316747219854113/50000000000000000000)
  directionLo := (560700066045551888103/100000000000000000000)
  directionHi := (70087508255693986013/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree127.table
  base := (95678566996969540662939853471041242973493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4097994965835489250629846029537564000000000000)
      constant := (139947622114496383774098657612785640534325147733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree127.table
  base := (95678566996317309226671885206242522747813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-603062932841475575769080246081285208000000000000)
      constant := (20615902199655685056784762030041496727513641288991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560700066045551888103/100000000000000000000)
  centralHi := (70087508255693986013/12500000000000000000)
  directionLo := (28146033452837173081/5000000000000000000)
  directionHi := (562920669056743461621/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree128.table
  base := (6129494187844768345004591492981030154011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4130249787945182612154131245096484000000000000)
      constant := (142197808370132425569487124062158982050517671856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree128.table
  base := (98071907004961847093493794328867442335981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-202603190072695333713639277746278116000000000000)
      constant := (6982456262162898734709598639536066846685221316989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28146033452837173081/5000000000000000000)
  centralHi := (562920669056743461621/100000000000000000000)
  directionLo := (282566273305527893719/50000000000000000000)
  directionHi := (565132546611055787439/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree129.table
  base := (25123196368611907293860500676118539476361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4162504610054875973678416460655404000000000000)
      constant := (144466019426127131954822836296948991691467699364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree129.table
  base := (5024639273698816775637333853564390055883/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-204185402531565475504251806798794496000000000000)
      constant := (7093830141149763220982846223585590658590404816540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282566273305527893719/50000000000000000000)
  centralHi := (565132546611055787439/100000000000000000000)
  directionLo := (283667900381283266463/50000000000000000000)
  directionHi := (567335800762566532927/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree130.table
  base := (20588240480755029975179705952107014398391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4194759432164569335202701676214324000000000000)
      constant := (146752255282481009727850582823990052479680586355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree130.table
  base := (20588240480674912339357232562676892886171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-617302844971306851884593007553932628000000000000)
      constant := (21618267110537553962409757504787769718248214056485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283667900381283266463/50000000000000000000)
  centralHi := (567335800762566532927/100000000000000000000)
  directionLo := (284765265795667236879/50000000000000000000)
  directionHi := (569530531591334473759/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree131.table
  base := (26354289448380684714871754933962340392901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4227014254274262696726986891773244000000000000)
      constant := (149056515939195102132291362501277939962809234324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree131.table
  base := (105417157793182268319470578661208809114881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-207349827449305759085476864903827256000000000000)
      constant := (7319232949251218132991920947296716668556408731089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284765265795667236879/50000000000000000000)
  centralHi := (569530531591334473759/100000000000000000000)
  directionLo := (142929209314111482601/25000000000000000000)
  directionHi := (114343367451289186081/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree132.table
  base := (6745040727732766462810197539132603556723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-35200570879206248415299769482084000000000000)
      constant := (1251064474349346186154946301951677918143632048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree132.table
  base := (107920651643434904944577197489422762540673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-1726711073621288436992474330217716000000000000)
      constant := (61431916350131731675175404615317671246581964697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142929209314111482601/25000000000000000000)
  centralHi := (114343367451289186081/20000000000000000000)
  directionLo := (573894814047242395773/100000000000000000000)
  directionHi := (286947407023621197887/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree133.table
  base := (27612920988605412516745550848679967294077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-11887877835162463766691294523244000000000000)
      constant := (425814713722188920495999720071873104170333268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree133.table
  base := (55225841977087872234809821126979081665197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3630000000000000000000000000000000000000000
      center := (52998)
      previous := (26499)
      next := (26499)
      square := (256979509806827844109466951580000000000000)
      linear := (-35702569794852062185545014926032000000000000)
      constant := (1280147406443005507357884539100907813288933022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573894814047242395773/100000000000000000000)
  centralHi := (286947407023621197887/50000000000000000000)
  directionLo := (576064556432804998081/100000000000000000000)
  directionHi := (288032278216402499041/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree134.table
  base := (28252563681415818329482613845561402572713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4323778720603342781299842538450004000000000000)
      constant := (156077446711515150500541858021602246503114706212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree134.table
  base := (11301025472545430686556261266688422291827/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-212096464825916184457314452061376396000000000000)
      constant := (7663974786723829945567602427450382181323354641630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576064556432804998081/100000000000000000000)
  centralHi := (288032278216402499041/50000000000000000000)
  directionLo := (289113078554883876391/50000000000000000000)
  directionHi := (578226157109767752783/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree135.table
  base := (5779818197875130402246226302522271545383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4356033542713036142824127754008924000000000000)
      constant := (158453806569688074965750520381019746867477496460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree135.table
  base := (115596363957325041564435751209429449805479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-213678677284786326247926981113892776000000000000)
      constant := (7780658765967221491621795482496531037050703281751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289113078554883876391/50000000000000000000)
  centralHi := (578226157109767752783/100000000000000000000)
  directionLo := (145094926762132018371/25000000000000000000)
  directionHi := (116075941409705614697/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree136.table
  base := (59105005824998552065818049900126769811759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4388288364822729504348412969567844000000000000)
      constant := (160848191228231483163050548870515898864294889758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree136.table
  base := (59105005824923113747418583218610577686799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-645782669230969404115618530499227468000000000000)
      constant := (23694683285761222549377730922604596429317497732986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145094926762132018371/25000000000000000000)
  centralHi := (116075941409705614697/20000000000000000000)
  directionLo := (227548943569499891/39062500000000000)
  directionHi := (582525295537919720961/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree137.table
  base := (60425598901603623957993101680290638529989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4420543186932422865872698185126764000000000000)
      constant := (163260600687148017196168671858636278763256899018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree137.table
  base := (60425598901539528106554580816814632422687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-216843102202526609829152039218925536000000000000)
      constant := (8016681774583518992590203721901708702967828303006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227548943569499891/39062500000000000)
  centralHi := (582525295537919720961/100000000000000000000)
  directionLo := (58466301022841025973/10000000000000000000)
  directionHi := (584663010228410259731/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree138.table
  base := (24703984483439156169505993383904077749473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4452798009042116227396983400685684000000000000)
      constant := (165691034946440417674362906987126922100873650565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree138.table
  base := (2470398448341737380276861229978749688323/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-218425314661396751619764568271441916000000000000)
      constant := (8136020803956691493758038864654482252582310559350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58466301022841025973/10000000000000000000)
  centralHi := (584663010228410259731/100000000000000000000)
  directionLo := (293396468586941076023/50000000000000000000)
  directionHi := (586792937173882152047/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree139.table
  base := (25243237098405410066740488013339220007121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4485052831151809588921268616244604000000000000)
      constant := (168139494006111495356737424657112248345655262005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree139.table
  base := (63108092745967261743032685122676463243757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-660022581360800680231131291971874888000000000000)
      constant := (24768734550120191517407148416762090950739461557998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293396468586941076023/50000000000000000000)
  centralHi := (586792937173882152047/100000000000000000000)
  directionLo := (117783032174410767771/20000000000000000000)
  directionHi := (73614395109006729857/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree140.table
  base := (128939987027766471697940118611638126289859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4517307653261502950445553831803524000000000000)
      constant := (170605977866164107650035254442048324994467330979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree140.table
  base := (16117498378460983605601103413842478067971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4522239583247694595938563803601524000000000000)
      constant := (170966406384362795313097264370984386275896330008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117783032174410767771/20000000000000000000)
  centralHi := (73614395109006729857/12500000000000000000)
  directionLo := (591029764303594526897/100000000000000000000)
  directionHi := (295514882151797263449/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree141.table
  base := (32922831756120020872413463435194608841001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4549562475371196311969839047362444000000000000)
      constant := (173090486526601139184133211732609686835135058724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree141.table
  base := (65845663512206656312309505348397361415831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-223171952038007176991602155428991056000000000000)
      constant := (8499347992337973024004496094669009315112481563278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591029764303594526897/100000000000000000000)
  centralHi := (295514882151797263449/50000000000000000000)
  directionLo := (593136828969983911319/100000000000000000000)
  directionHi := (14828420724249597783/2500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree142.table
  base := (134470205482234181182768488053249347975429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4581817297480889673494124262921364000000000000)
      constant := (175593019987425485811627807578369032768914714149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree142.table
  base := (134470205482177464067029280260016335398539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-674262493490631956346644053444522308000000000000)
      constant := (25866681265658383705438794228887143327341906562673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593136828969983911319/100000000000000000000)
  centralHi := (14828420724249597783/2500000000000000000)
  directionLo := (595236434930165705583/100000000000000000000)
  directionHi := (37202277183135356599/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree143.table
  base := (4289894450034219270549345619703056687157/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-38132827434632917644780243623804000000000000)
      constant := (1472013043377190425462001731789241710850037664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree143.table
  base := (68638311200523420924185094007302437016381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-1870548569882210417957249698628296000000000000)
      constant := (72280919020482512217188519391259768616765527018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595236434930165705583/100000000000000000000)
  centralHi := (37202277183135356599/6250000000000000000)
  directionLo := (298664330418020808607/50000000000000000000)
  directionHi := (119465732167208323443/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree144.table
  base := (140110577781128552848747115844031922879111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4646326941700276396542694694039204000000000000)
      constant := (180652161310247687518905368661523574423282447591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree144.table
  base := (35027644445271908936274603739951869022701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-227918589414617602363439742586540196000000000000)
      constant := (8870640331114882923950779214662839591792998066676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298664330418020808607/50000000000000000000)
  centralHi := (119465732167208323443/20000000000000000000)
  directionLo := (299706791983425145797/50000000000000000000)
  directionHi := (119882716793370058319/20000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree145.table
  base := (71486035811200132309173835209135774760003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4678581763809969758066979909598124000000000000)
      constant := (183208769172251283933087583624149999554583382086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree145.table
  base := (71486035811182756739080673047928505271911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-688502405620463232462156814917169728000000000000)
      constant := (26988523432387295875940158844227501906402009250954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299706791983425145797/50000000000000000000)
  centralHi := (119882716793370058319/20000000000000000000)
  directionLo := (601491280262473739691/100000000000000000000)
  directionHi := (150372820065618434923/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree146.table
  base := (145861103924974978325869119603205386452487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4710836585919663119591265125157044000000000000)
      constant := (185783401834653662403657667062237078485631084647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree146.table
  base := (145861103924945465363839211654913482011261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-231083014332357885944664800691572956000000000000)
      constant := (9122593640521170185625898446683193210578960695309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601491280262473739691/100000000000000000000)
  centralHi := (150372820065618434923/25000000000000000000)
  directionLo := (9430653505557997859/1562500000000000000)
  directionHi := (603561824355711862977/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree147.table
  base := (29755534937783348751639403020142555004109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4743091408029356481115550340715964000000000000)
      constant := (188376059297457620689356566759674602725672426145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree147.table
  base := (37194418672222920141642260091509779716787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4748269934514857708883210811103864000000000000)
      constant := (188773424903902754967061482229157377751235891788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9430653505557997859/1562500000000000000)
  centralHi := (603561824355711862977/100000000000000000000)
  directionLo := (605625289603563883589/100000000000000000000)
  directionHi := (60562528960356388359/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree148.table
  base := (948261149464304581791566942029676303777/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4775346230139049842639835556274884000000000000)
      constant := (190986741560665918213799683410409918500045301920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree148.table
  base := (151721783914267449733637088655578554751997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-702742317750294508577669576389817148000000000000)
      constant := (28134261050318285541799510799280163110967931200679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605625289603563883589/100000000000000000000)
  centralHi := (60562528960356388359/10000000000000000000)
  directionLo := (37980109257347110921/6250000000000000000)
  directionHi := (607681748117553774737/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree149.table
  base := (154693431601153162364414760292748541427407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4807601052248743204164120771833804000000000000)
      constant := (193615448624281272636406171509742485038090565167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree149.table
  base := (154693431601135089621151528547592430146729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-235829651708968311316502387849122096000000000000)
      constant := (9507161229965884128120325850324188441120724203001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37980109257347110921/6250000000000000000)
  centralHi := (607681748117553774737/100000000000000000000)
  directionLo := (609731270793135159723/100000000000000000000)
  directionHi := (152432817698283789931/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree150.table
  base := (157692617749571231790945899904983748552337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4839855874358436565688405987392724000000000000)
      constant := (196262180488306357243088500747268195120514632497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree150.table
  base := (78846308874777943009838746164809059993997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-237411864167838453107114916901638476000000000000)
      constant := (9637120459870733010153745482550257805860582729786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609731270793135159723/100000000000000000000)
  centralHi := (152432817698283789931/25000000000000000000)
  directionLo := (611773927338209603347/100000000000000000000)
  directionHi := (152943481834552400837/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree151.table
  base := (160719342359603081570998379515490513977203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4872110696468129927212691202951644000000000000)
      constant := (198926937152743799018130541515229325141038204243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree151.table
  base := (160719342359590051876823155120684130926667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-716982229880125784693182337862464568000000000000)
      constant := (29303894119462312113879664975828807170882137960369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611773927338209603347/100000000000000000000)
  centralHi := (152943481834552400837/25000000000000000000)
  directionLo := (153452446575197687917/25000000000000000000)
  directionHi := (613809786300790751669/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree152.table
  base := (81886802715653880351192440104334374383487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (17666)
      previous := (8833)
      next := (8833)
      square := (85659836602275948036488983860000000000000)
      linear := (-13585500051462114373232621657924000000000000)
      constant := (558475674840986640667051937773056918600803854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree152.table
  base := (163773605431296698010185922683710982477023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (865634)
      previous := (432817)
      next := (432817)
      square := (4197331993511521453787960209140000000000000)
      linear := (-666416313256450794150526246555876000000000000)
      constant := (27422974985640231940444056842874234415106269367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153452446575197687917/25000000000000000000)
  centralHi := (613809786300790751669/100000000000000000000)
  directionLo := (7697986438698067267/1250000000000000000)
  directionHi := (615838915095845381361/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree153.table
  base := (166855406964743206453311108272488678566251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-4936620340687516650261261634069484000000000000)
      constant := (204310524882866022788926618266165689968452409931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree153.table
  base := (41713851741183453555492427852912510261489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-242158501544448878478952504059187616000000000000)
      constant := (10032308249856916207349947461880311429703491797764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7697986438698067267/1250000000000000000)
  centralHi := (615838915095845381361/100000000000000000000)
  directionLo := (617861380031341093661/100000000000000000000)
  directionHi := (308930690015670546831/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree154.table
  base := (84982373479983116324799662581841062817289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-41065083990059586874260717765524000000000000)
      constant := (1710986412797981960555528015770225247354082658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree154.table
  base := (84982373479979129489275379986871602986021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (158118)
      previous := (79059)
      next := (79059)
      square := (766690934217064890277004706780000000000000)
      linear := (-123329759151620350954409697981972000000000000)
      constant := (5143771738881735452828960900827451892067721486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617861380031341093661/100000000000000000000)
  centralHi := (308930690015670546831/50000000000000000000)
  directionLo := (77484655791691140841/12500000000000000000)
  directionHi := (619877246333529126729/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree155.table
  base := (43275406354258131298724861296986995523423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5001129984906903373309832065187324000000000000)
      constant := (209766211814667993011639896368955475805834560252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree155.table
  base := (34620325083405151222931358686392447539079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-245322926462189162060177562164220376000000000000)
      constant := (10300191860075303877841783661805794037733854900755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77484655791691140841/12500000000000000000)
  centralHi := (619877246333529126729/100000000000000000000)
  directionLo := (124377315634297912051/20000000000000000000)
  directionHi := (9716977783929524379/1562500000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree156.table
  base := (176266042335996643501972858026670958555513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5033384807016596734834117280746244000000000000)
      constant := (212521092481204933351898467911112918140663363353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree156.table
  base := (5508313822999715539730145306643899711981/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-246905138921059303850790091216736756000000000000)
      constant := (10435461190253135187308609257021239959444257951648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124377315634297912051/20000000000000000000)
  centralHi := (9716977783929524379/1562500000000000000)
  directionLo := (623889438680965044297/100000000000000000000)
  directionHi := (311944719340482522149/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree157.table
  base := (22432249714614003340978329432136660148273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5065639629126290096358402496305164000000000000)
      constant := (215293997948168972523811830436971299615493703304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree157.table
  base := (44864499429226787246794216985440457645281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-745462054139788336924207860807759408000000000000)
      constant := (31714846611430634599388983959518960043677269384268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623889438680965044297/100000000000000000000)
  centralHi := (311944719340482522149/50000000000000000000)
  directionLo := (625885889987508097087/100000000000000000000)
  directionHi := (9779467031054814017/1562500000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree158.table
  base := (4566937288995775097155034748138686980197/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5097894451235983457882687711864084000000000000)
      constant := (218084928215562396311029187638798871439279406280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree158.table
  base := (182677491559826863538215479287205170410819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-250069563838799587432015149321769516000000000000)
      constant := (10708654900746644968493830886631677491387034252211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625885889987508097087/100000000000000000000)
  centralHi := (9779467031054814017/1562500000000000000)
  directionLo := (125575198645793196273/20000000000000000000)
  directionHi := (313937996614482990683/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree159.table
  base := (185924523864804807063010277186552512975531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5130149273345676819406972927423004000000000000)
      constant := (220893883283387442582295312073108776319284169611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree159.table
  base := (18592452386480129277230468718912223452139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-251651776297669729222627678374285896000000000000)
      constant := (10846579281062545191267393599676346006980312992910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125575198645793196273/20000000000000000000)
  centralHi := (313937996614482990683/50000000000000000000)
  directionLo := (314929904288663091267/50000000000000000000)
  directionHi := (125971961715465236507/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree160.table
  base := (47299773657970896772072186920944942550437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5162404095455370180931258142981924000000000000)
      constant := (223720863151646301976016982250731024142182554388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree160.table
  base := (23649886828985075538351932044343333818459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-759701966269619613039720622280406828000000000000)
      constant := (32956166034274058735990122399999347609480350512904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314929904288663091267/50000000000000000000)
  centralHi := (125971961715465236507/20000000000000000000)
  directionLo := (631837395259944572177/100000000000000000000)
  directionHi := (315918697629972286089/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree161.table
  base := (96250601930558215562919309160222288976619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5194658917565063542455543358540844000000000000)
      constant := (226565867820341118668596225335814963609575389078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree161.table
  base := (96250601930556949782667022976895957216421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5200330637049183934772504826108544000000000000)
      constant := (227042512078228025017279028276628723614340971402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631837395259944572177/100000000000000000000)
  centralHi := (315918697629972286089/50000000000000000000)
  directionLo := (316904405790088722359/50000000000000000000)
  directionHi := (633808811580177444719/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree162.table
  base := (97915425776275690866117507340951091674649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5226913739674756903979828574099764000000000000)
      constant := (229428897289473991206946799389054497270880685938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree162.table
  base := (195830851552549233216629140959633798167117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-256398413674280154594465265531835036000000000000)
      constant := (11265662522288108987540626117829200224949154046173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316904405790088722359/50000000000000000000)
  centralHi := (633808811580177444719/100000000000000000000)
  directionLo := (158943528734359440217/25000000000000000000)
  directionHi := (635774114937437760869/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree163.table
  base := (49797009426558864253227063297155968856719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5259168561784450265504113789658684000000000000)
      constant := (232309951559046973388932006062012231502521370556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree163.table
  base := (39837607541246726730734427901858841437401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-773941878399450889155233383753054248000000000000)
      constant := (34221380908368782565579013385846300707827928114535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158943528734359440217/25000000000000000000)
  centralHi := (635774114937437760869/100000000000000000000)
  directionLo := (318866680923347558447/50000000000000000000)
  directionHi := (127546672369339023379/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree164.table
  base := (50643190580553667891722309085966141601457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5291423383894143627028399005217604000000000000)
      constant := (235209030629062075178252114206932844125172972868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree164.table
  base := (202572762322213124212840901131356840662803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-259562838592020438175690323636867796000000000000)
      constant := (11549476433337727335726267160734842653692602994307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318866680923347558447/50000000000000000000)
  centralHi := (127546672369339023379/20000000000000000000)
  directionLo := (639686607957438181523/100000000000000000000)
  directionHi := (159921651989359545381/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree165.table
  base := (411970050801068115930868221964201386093/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (52706)
      previous := (26353)
      next := (26353)
      square := (255563644739021630092334902260000000000000)
      linear := (-43997340545486256103741191907244000000000000)
      constant := (1967984582640671600352497219617298350189786500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree165.table
  base := (41197005080106548977157491769911996703561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 176890000000000000000000000000000000000000000
      center := (2582594)
      previous := (1291297)
      next := (1291297)
      square := (12522618592212059874524410210740000000000000)
      linear := (-2158223562404054379886800435449456000000000000)
      constant := (96633974495310783730101706483127381548446452645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639686607957438181523/100000000000000000000)
  centralHi := (159921651989359545381/25000000000000000000)
  directionLo := (128326781614423520123/20000000000000000000)
  directionHi := (80204238509014700077/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree166.table
  base := (209424826941237688554738555080703483717349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5355933028113530350076969436335444000000000000)
      constant := (241061263170426463906286327572022552872257521669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree166.table
  base := (3272262920956821473755598851616908434543/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-788181790529282165270746145225701668000000000000)
      constant := (35510491233722963059837605084299349740313798342464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128326781614423520123/20000000000000000000)
  centralHi := (80204238509014700077/12500000000000000000)
  directionLo := (160893829041021665411/25000000000000000000)
  directionHi := (128715063232817332329/20000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree167.table
  base := (212892166944368697410677161893119934067453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5388187850223223711601254651894364000000000000)
      constant := (244014416641779560108722884309825019840000414493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree167.table
  base := (8515686677774710077750271647966372151963/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21403690000000000000000000000000000000000000000
      center := (312493874)
      previous := (156246937)
      next := (156246937)
      square := (1515236849657659244817453635499540000000000000)
      linear := (-264309475968630863547527910794416936000000000000)
      constant := (11981834925262968235829616464078812046913122358675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160893829041021665411/25000000000000000000)
  centralHi := (128715063232817332329/20000000000000000000)
  directionLo := (64551088539505633397/10000000000000000000)
  directionHi := (645510885395056333971/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree168.table
  base := (216387045409969302305108004761457210230677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5420442672332917073125539867453284000000000000)
      constant := (246985594913582396364454366288757084400086202037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree168.table
  base := (108193522704984250035977426333306075105383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5426360988316347047717151833610884000000000000)
      constant := (247504580734666058169995213581339677333356469646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell113.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64551088539505633397/10000000000000000000)
  centralHi := (645510885395056333971/100000000000000000000)
  directionLo := (647440668132080655067/100000000000000000000)
  directionHi := (161860167033020163767/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 109
  qDenominator := 209
  table := BinomialMassData.Q109_209.Degree169.table
  base := (219909462338080826569735205245842422446111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (6377426)
      previous := (3188713)
      next := (3188713)
      square := (30923201013421617241172523173460000000000000)
      linear := (-5452697494442610434649825083012204000000000000)
      constant := (249974797985836777717932941242686658854868574591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q109_209.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 4583
  qDenominator := 8778
  table := BinomialMassData.Q4583_8778.Degree169.table
  base := (8796378493523205835805852556907746866367/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64211070000000000000000000000000000000000000000
      center := (937481622)
      previous := (468740811)
      next := (468740811)
      square := (4545710548972977734452360906498620000000000000)
      linear := (-802421702659113441386258906698349088000000000000)
      constant := (36823497010344245956649189856868974890946430206725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4583_8778.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell113.Kernel169
