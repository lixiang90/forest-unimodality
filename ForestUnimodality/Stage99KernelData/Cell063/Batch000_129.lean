import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell063.Parameters
import ForestUnimodality.BinomialMassData.Q405_808.Batch000_049
import ForestUnimodality.BinomialMassData.Q405_808.Batch050_099
import ForestUnimodality.BinomialMassData.Q405_808.Batch100_149
import ForestUnimodality.BinomialMassData.Q203_404.Batch000_049
import ForestUnimodality.BinomialMassData.Q203_404.Batch050_099
import ForestUnimodality.BinomialMassData.Q203_404.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree000.table
  base := (123843952726111892073106447/2000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (392405802558197028262476635000000000000)
      linear := (-2237617837918361228359553900000000000)
      constant := (309609881815279730182766117500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree000.table
  base := (123843952726111892073106447/2000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (392405802558197028262476635000000000000)
      linear := (-2237617837918361228359553900000000000)
      constant := (309609881815279730182766117500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree001.table
  base := (87221058532512285680056650423385692311109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-4035665777975367563159647498002650000000000)
      constant := (1780501170552595162945908299289072878906245818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree001.table
  base := (43527386536719454539371395443855593680307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-4045574024489962038123275033036400000000000)
      constant := (1777113615383784629398180958652718757031246828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12499846827803811301/25000000000000000000)
  directionHi := (9999877462243049041/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree002.table
  base := (206526351748271722586367535327245944408023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-16097011232772259846857598373342800000000000)
      constant := (2114866624283525900831652342906360003906242623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree002.table
  base := (205828713049442398104543374414390662144029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-16136644218830637746712108513477800000000000)
      constant := (2107789905054703113893546218160668344531239829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499846827803811301/25000000000000000000)
  centralHi := (9999877462243049041/20000000000000000000)
  directionLo := (35354905822932919159/50000000000000000000)
  directionHi := (70709811645865838319/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree003.table
  base := (25934599889793403109838325424605518699673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-24122690909593784567395901750680300000000000)
      constant := (1340965391443453638793300029274428950026821365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree003.table
  base := (129111599343073241639976415173821811862499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-24182140388681351417177666960882800000000000)
      constant := (1335328223773809732214673944696753227809352299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354905822932919159/50000000000000000000)
  centralHi := (70709811645865838319/100000000000000000000)
  directionLo := (86601479170339441739/100000000000000000000)
  directionHi := (4330073958516972087/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree004.table
  base := (3466652091961221318881733746612882156847/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-32148370586415309287934205128017800000000000)
      constant := (916356660392374651194236561310167272049906175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree004.table
  base := (43125723329364005323114395652206195900301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-16113818279266032543821612704143900000000000)
      constant := (456142032278993799799023405633482104378970501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/100000000000000000000)
  centralHi := (4330073958516972087/5000000000000000000)
  directionLo := (99998774622430490409/100000000000000000000)
  directionHi := (9999877462243049041/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree005.table
  base := (61415100804302292162606692778888785904499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-40174050263236834008472508505355300000000000)
      constant := (676894513130362954590146502833946223761794299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree005.table
  base := (61114853439870836800592494704580733364177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-40273132728382778758108783855692800000000000)
      constant := (674080598129014323283720427227066686047969577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99998774622430490409/100000000000000000000)
  centralHi := (9999877462243049041/10000000000000000000)
  directionLo := (111802028861217721361/100000000000000000000)
  directionHi := (55901014430608860681/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree006.table
  base := (2854844513473552646132987700742328195989/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-24099864970029179364505405941346400000000000)
      constant := (269251751866386872773078806602819231918270312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree006.table
  base := (45457351358187044120189205927561458142809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-48318628898233492428574342303097800000000000)
      constant := (536616003069751893570353055900607034514794609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111802028861217721361/100000000000000000000)
  centralHi := (55901014430608860681/50000000000000000000)
  directionLo := (30618246591066282437/25000000000000000000)
  directionHi := (122472986364265129749/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree007.table
  base := (7041072360359592894385480145731621691177/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-56225409616879883449549115260030300000000000)
      constant := (457848001768102533771114615947589083108482885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree007.table
  base := (35038726640016380848580841123755313357503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-56364125068084206099039900750502800000000000)
      constant := (456635858675092082290519803937823276559888103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30618246591066282437/25000000000000000000)
  centralHi := (122472986364265129749/100000000000000000000)
  directionLo := (66142972265536994977/50000000000000000000)
  directionHi := (26457188906214797991/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree008.table
  base := (1111061774154249707210674190744585718683/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-64251089293701408170087418637367800000000000)
      constant := (412260311998224167834999740710946972907132075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree008.table
  base := (13822724505601034758260012908556338338717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-32204810618967459884752729598953900000000000)
      constant := (205779971309180801240214102154266607393252117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66142972265536994977/50000000000000000000)
  centralHi := (26457188906214797991/20000000000000000000)
  directionLo := (141419623291731676637/100000000000000000000)
  directionHi := (70709811645865838319/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree009.table
  base := (1110217810304346826186617801078465072449/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-36138384485261466445312861007352650000000000)
      constant := (194817435164846315257676359361295456415522490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree009.table
  base := (22097367523758558923399352246460037790987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-72455117407785633439971017645312800000000000)
      constant := (389349535079159846342682090441005870505858387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/100000000000000000000)
  centralHi := (70709811645865838319/50000000000000000000)
  directionLo := (74999080966822867807/50000000000000000000)
  directionHi := (29999632386729147123/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree010.table
  base := (8917974883389971472537648486260163656477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-40151224323672228805582012696021400000000000)
      constant := (191655989239736580262590252360993991959721877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree010.table
  base := (2218252351976017953770151319705289576587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-40250306788818173555218288046358900000000000)
      constant := (191694830651486170346727392106502635883055948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/50000000000000000000)
  centralHi := (29999632386729147123/20000000000000000000)
  directionLo := (79055972758181150399/50000000000000000000)
  directionHi := (158111945516362300799/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree011.table
  base := (14297375523565656158782335119088628766709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-88328128324165982331702328769380300000000000)
      constant := (389476977471883409246461491842369070799198509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree011.table
  base := (14220183266917270040190319271677809509813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-88546109747487060780902134540122800000000000)
      constant := (389893509941756405293673799257439059809602413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/50000000000000000000)
  centralHi := (158111945516362300799/100000000000000000000)
  directionLo := (82914603729478850989/50000000000000000000)
  directionHi := (165829207458957701979/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree012.table
  base := (11363302069053651542699981180077873750979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-96353808000987507052240632146717800000000000)
      constant := (405831261620133655108607935926250390133736779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree012.table
  base := (5648077453723339239035108277189788850711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-48295802958668887225683846493763900000000000)
      constant := (203289528199610976097207904201883136066102911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/50000000000000000000)
  centralHi := (165829207458957701979/100000000000000000000)
  directionLo := (86601479170339441739/50000000000000000000)
  directionHi := (173202958340678883479/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree013.table
  base := (8889894169312032471981003361992999238743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-104379487677809031772778935524055300000000000)
      constant := (430907567702884620641553225448188803984417343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree013.table
  base := (110387991070176661762652489027130253339/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-52318551043594244060916625717466400000000000)
      constant := (215994317186369195965616624728107941072445560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/50000000000000000000)
  centralHi := (173202958340678883479/100000000000000000000)
  directionLo := (90137677346185064761/50000000000000000000)
  directionHi := (180275354692370129523/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree014.table
  base := (54238297456936143771438467186759015311/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-112405167354630556493317238901392800000000000)
      constant := (463712679004811516117327113496728714398438875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree014.table
  base := (1345601721547521416554152012885516829757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-112682598257039201792298809882337800000000000)
      constant := (465134503538955373746075706419525185901755785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90137677346185064761/50000000000000000000)
  centralHi := (180275354692370129523/100000000000000000000)
  directionLo := (3741611537343595959/2000000000000000000)
  directionHi := (187080576867179797951/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree015.table
  base := (310216012907428263770464902477702406527/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-60215423515726040606927771139365150000000000)
      constant := (251768686005662941204387755524609947366855416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree015.table
  base := (4917845252918613449246706924810096259023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-120728094426889915462764368329742800000000000)
      constant := (505310574947087427119677317046559916938293623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/2000000000000000000)
  centralHi := (187080576867179797951/100000000000000000000)
  directionLo := (48411698594227770219/25000000000000000000)
  directionHi := (193646794376911080877/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree016.table
  base := (1694513586705071500452294725441780922977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-64228263354136802967196922828033900000000000)
      constant := (274926239671731605751216873822290607195288377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree016.table
  base := (3348855911932617624002454424540922414987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-128773590596740629133229926777147800000000000)
      constant := (551989525149735076469958273908515549555282387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/25000000000000000000)
  centralHi := (193646794376911080877/100000000000000000000)
  directionLo := (199997549244860980819/100000000000000000000)
  directionHi := (9999877462243049041/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree017.table
  base := (2016489048499879899469710314811542299309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-136482206385095130654932149033405300000000000)
      constant := (602249848440420906168234310335701511745251109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree017.table
  base := (396228475016458434675404540822829135259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-136819086766591342803695485224552800000000000)
      constant := (604764352509775884646142921458572225043885295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/100000000000000000000)
  centralHi := (9999877462243049041/5000000000000000000)
  directionLo := (206152755100307852147/100000000000000000000)
  directionHi := (51538188775076963037/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree018.table
  base := (101780457687553677265358769481508242993/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-72253943030958327687735226205371400000000000)
      constant := (330203573183547408547050002130419524847086372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree018.table
  base := (783183539743328946137474699386830315879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-144864582936442056474161043671957800000000000)
      constant := (663313510259339284197504068705407856052281679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/100000000000000000000)
  centralHi := (51538188775076963037/25000000000000000000)
  directionLo := (53032358734399378739/25000000000000000000)
  directionHi := (212129434937597514957/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree019.table
  base := (-243068891816370669619076108014961108011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-152533565738738180096008755788080300000000000)
      constant := (724065676740453461407676266438306850487179789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree019.table
  base := (-33790264439504691953265505505956164097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-76455039553146385072313301059681400000000000)
      constant := (363689448789149917741941237139810227180186012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/25000000000000000000)
  centralHi := (212129434937597514957/100000000000000000000)
  directionLo := (43588455305707418143/20000000000000000000)
  directionHi := (54485569132134272679/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree020.table
  base := (-1176022559570986086546047687333384842099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-160559245415559704816547059165417800000000000)
      constant := (793015564715719968270783131001347141225748101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree020.table
  base := (-239980025973089596427610105110021476933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-160955575276143483815092160566767800000000000)
      constant := (796751133441588033620280288510730354569032335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43588455305707418143/20000000000000000000)
  centralHi := (54485569132134272679/25000000000000000000)
  directionLo := (223604057722435442723/100000000000000000000)
  directionHi := (55901014430608860681/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree021.table
  base := (-1000714442710286526517090417273328570659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-84292462546190614768542681271377650000000000)
      constant := (433542657868023843539681816019392134625707541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree021.table
  base := (-2022319376416878788605851711527922299257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-169001071445994197485557719014172800000000000)
      constant := (871259158574588607399185324794415889625279343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/100000000000000000000)
  centralHi := (55901014430608860681/25000000000000000000)
  directionLo := (114562988527529205487/50000000000000000000)
  directionHi := (9165039082202336439/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree022.table
  base := (-2733091683785380066790071608139608581447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-176610604769202754257623665920092800000000000)
      constant := (946134117090535662908312783158014477860659153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree022.table
  base := (-550268961315757919992064141692312613287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-177046567615844911156023277461577800000000000)
      constant := (950762556707983859982658562651469795159296565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114562988527529205487/50000000000000000000)
  centralHi := (9165039082202336439/4000000000000000000)
  directionLo := (234517914226039596771/100000000000000000000)
  directionHi := (58629478556509899193/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree023.table
  base := (-1691191567562327486387139763084592141121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-92318142223012139489080984648715150000000000)
      constant := (515022980583159554245593958357669434943424679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree023.table
  base := (-3398312741462184160603164306998197322383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-185092063785695624826488835908982800000000000)
      constant := (1035145686030120442174058191110500314114371017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234517914226039596771/100000000000000000000)
  centralHi := (58629478556509899193/25000000000000000000)
  directionLo := (239788637813448069871/100000000000000000000)
  directionHi := (14986789863340504367/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree024.table
  base := (-3958694715113369722050200300155270423411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-192661964122845803698700272674767800000000000)
      constant := (1118725045520037634955191333057543086410784389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree024.table
  base := (-496572688293284568780534990066301606769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-96568779977773169248477197178193900000000000)
      constant := (562156541132412545573131773328744829237397724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/100000000000000000000)
  centralHi := (14986789863340504367/6250000000000000000)
  directionLo := (244945972728530259497/100000000000000000000)
  directionHi := (122472986364265129749/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree025.table
  base := (-4469796310848346983811481883619585516441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-200687643799667328419238576052105300000000000)
      constant := (1212092109533416554251878629410752076896785359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree025.table
  base := (-560236306338502695650140641255889838061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-100591528062698526083709976401896400000000000)
      constant := (609092898154041695511020122254384983547758956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/100000000000000000000)
  centralHi := (122472986364265129749/50000000000000000000)
  directionLo := (31249617069509528253/12500000000000000000)
  directionHi := (9999877462243049041/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree026.table
  base := (-615265696414787766638921096967920005193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-104356661738244426569888439714721400000000000)
      constant := (655040741374560990420165829319409054608104828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree026.table
  base := (-2466324627225579582675463820443688625463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-104614276147623882918942755625598900000000000)
      constant := (658349221507598645235340342421088732331651937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31249617069509528253/12500000000000000000)
  centralHi := (9999877462243049041/4000000000000000000)
  directionLo := (254947851567570017351/100000000000000000000)
  directionHi := (31868481445946252169/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree027.table
  base := (-2660511435293356662942965801517892607951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-108369501576655188930157591403390150000000000)
      constant := (706319344005666187025923282140360461881291849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree027.table
  base := (-1332543209219569663649458230218459222073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-108637024232549239754175534849301400000000000)
      constant := (709898402447180538001529339870226657451266654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254947851567570017351/100000000000000000000)
  centralHi := (31868481445946252169/12500000000000000000)
  directionLo := (259804437511018325217/100000000000000000000)
  directionHi := (129902218755509162609/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree028.table
  base := (-177216347272388807489809491499065451859/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-112382341415065951290426743092058900000000000)
      constant := (759859242431851242997125363652935533209381456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree028.table
  base := (-1135774615456915962348999327094162714149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-225319544634949193178816628146007800000000000)
      constant := (1527435876364884414675603238260196030764830255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259804437511018325217/100000000000000000000)
  centralHi := (129902218755509162609/50000000000000000000)
  directionLo := (264571889062147979909/100000000000000000000)
  directionHi := (26457188906214797991/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree029.table
  base := (-2987756437787762288375134053789126238981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-116395181253476713650695894780727650000000000)
      constant := (815641633262700236113718523284792732611154819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree029.table
  base := (-5982415843282669093192884798815205699689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-233365040804799906849282186593412800000000000)
      constant := (1639578261911251108026573206591195111657472511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264571889062147979909/100000000000000000000)
  centralHi := (26457188906214797991/10000000000000000000)
  directionLo := (16828433807915238377/6250000000000000000)
  directionHi := (269254940926643814033/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree030.table
  base := (-155946487324968631427308051210159298721/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-120408021091887476010965046469396400000000000)
      constant := (873650871561988852011958556123893612374941580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree030.table
  base := (-1560962483222153385443491571825764234077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-120705268487325310259873872520408900000000000)
      constant := (878096430372449628076017284862667258096361046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828433807915238377/6250000000000000000)
  centralHi := (269254940926643814033/100000000000000000000)
  directionLo := (273857922917901650441/100000000000000000000)
  directionHi := (136928961458950825221/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree031.table
  base := (-6460517294686376772864493211125613991527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-248841721860596476742468396316130300000000000)
      constant := (1867747857942161697610721597773969830422433073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree031.table
  base := (-1293142631659596194620439147021971332207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-249456033144501334190213303488222800000000000)
      constant := (1877253784643621871764909376439390077200781965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273857922917901650441/100000000000000000000)
  centralHi := (136928961458950825221/50000000000000000000)
  directionLo := (278384806834719832723/100000000000000000000)
  directionHi := (69596201708679958181/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree032.table
  base := (-6645615182756673131418070553130789559583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-256867401537418001463006699693467800000000000)
      constant := (1992599894049444143858860004493748815702693817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree032.table
  base := (-831264969789028688955871620293406177989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-128750764657176023930339430967813900000000000)
      constant := (1001369733128702640268742639584201454313336844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278384806834719832723/100000000000000000000)
  centralHi := (69596201708679958181/25000000000000000000)
  directionLo := (141419623291731676637/50000000000000000000)
  directionHi := (11313569863338534131/4000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree033.table
  base := (-1698732229624150465962512569795454163771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-132446540607119763091772501535402650000000000)
      constant := (1060919868452468343491805937061184128525744058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree033.table
  base := (-6798832519566467747882068504801887726017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-265547025484202761531144420383032800000000000)
      constant := (2132631923399784739738339344676813368306900583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/50000000000000000000)
  centralHi := (11313569863338534131/4000000000000000000)
  directionLo := (287224612697794577817/100000000000000000000)
  directionHi := (143612306348897288909/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree034.table
  base := (-863742607233444763923574355791433977209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-136459380445530525452041653224071400000000000)
      constant := (1127726132497738567574654360717716390493963964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree034.table
  base := (-3456661175048779372215077550469690209459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-136796260827026737600804989415218900000000000)
      constant := (1133458075668938104632828844179766890173308741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287224612697794577817/100000000000000000000)
  centralHi := (143612306348897288909/50000000000000000000)
  directionLo := (145772011091717303553/50000000000000000000)
  directionHi := (291544022183434607107/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree035.table
  base := (-3495944683685918959886867652795111577269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-140472220283941287812310804912740150000000000)
      constant := (1196712422872187783196678244840792301175278931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree035.table
  base := (-3497408770177299634924239748168922657469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-140819008911952094436037768638921400000000000)
      constant := (1202789810140404226491693918082460882471158731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145772011091717303553/50000000000000000000)
  centralHi := (291544022183434607107/100000000000000000000)
  directionLo := (73950091109811995603/25000000000000000000)
  directionHi := (295800364439247982413/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree036.table
  base := (-440113108983936092592057065421859244897/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-144485060122352050172579956601408900000000000)
      constant := (1267873459044826589008197404621779410742445624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree036.table
  base := (-7044344537378573647647518882153668177673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-289683513993754902542541095725247800000000000)
      constant := (2548611859442316389807399410265991030919557727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73950091109811995603/25000000000000000000)
  centralHi := (295800364439247982413/100000000000000000000)
  directionLo := (74999080966822867807/25000000000000000000)
  directionHi := (299996323867291471229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree037.table
  base := (-7060568130466872174533273067595160517381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-296995799921525625065698216580155300000000000)
      constant := (2682409646501610351266964753998949486312196419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree037.table
  base := (-3531380863229230447860037976367309834959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-148864505081802808106503327086326400000000000)
      constant := (1348002056217033572388083965188849984873583241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/25000000000000000000)
  centralHi := (299996323867291471229/100000000000000000000)
  directionLo := (30413439967452834403/10000000000000000000)
  directionHi := (304134399674528344031/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree038.table
  base := (-7048889655543215464724056274561966216277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-305021479598347149786236519957492800000000000)
      constant := (2833405633949522213100754297461208007627758323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree038.table
  base := (-220337107664158657227013080662368738123/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-152887253166728164941736106310028900000000000)
      constant := (1423874525746801567849126932963200724038516432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30413439967452834403/10000000000000000000)
  centralHi := (304134399674528344031/100000000000000000000)
  directionLo := (308216923281124618007/100000000000000000000)
  directionHi := (38527115410140577251/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree039.table
  base := (-3503690897988064635338622357897859890037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-156523579637584337253387411667415150000000000)
      constant := (1494364341780234857912899295378600790636732563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree039.table
  base := (-3504511617964324004351534871788129104087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-156910001251653521776968885533731400000000000)
      constant := (1501920270144643345806296530016760557509208513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308216923281124618007/100000000000000000000)
  centralHi := (38527115410140577251/12500000000000000000)
  directionLo := (312246073679685475449/100000000000000000000)
  directionHi := (6244921473593709509/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree040.table
  base := (-6936553795684875697689922647066292754249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-321072838951990199227313126712167800000000000)
      constant := (3148373600537232466705962077393821747613905951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree040.table
  base := (-27101457662913258412866128900082427933/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-160932749336578878612201664757433900000000000)
      constant := (1582136718436102132288575659751170171539899776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312246073679685475449/100000000000000000000)
  centralHi := (6244921473593709509/2000000000000000000)
  directionLo := (79055972758181150399/25000000000000000000)
  directionHi := (316223891032724601597/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree041.table
  base := (-854604102157614309625648677418091178621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-164549259314405861973925715044752650000000000)
      constant := (1656168013697107492511416950445906441922548716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree041.table
  base := (-6838059867709689952247241764564587705349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-329910994843008470894868887962272800000000000)
      constant := (3329043429839433949660132010215330865817734851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/25000000000000000000)
  centralHi := (316223891032724601597/100000000000000000000)
  directionLo := (320152288749234767617/100000000000000000000)
  directionHi := (160076144374617383809/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree042.table
  base := (-6708577388185666141063115234005125045951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-337124198305633248668389733466842800000000000)
      constant := (3480612306792579299924992905126957844406253849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree042.table
  base := (-6709637946061980352422828592069310397187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-337956491012859184565334446409677800000000000)
      constant := (3498146901996742846746383023341304164638295413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320152288749234767617/100000000000000000000)
  centralHi := (160076144374617383809/50000000000000000000)
  directionLo := (324033064243250193093/100000000000000000000)
  directionHi := (162016532121625096547/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree043.table
  base := (-40950553774150802958711914815382428983/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-172574938991227386694464018422090150000000000)
      constant := (1826599683629049514511323727921478691730553360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree043.table
  base := (-3276502533408873328412940432348691620533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-173000993591354949117900002428541400000000000)
      constant := (1835790408405949535734013380687251459278942867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324033064243250193093/100000000000000000000)
  centralHi := (162016532121625096547/50000000000000000000)
  directionLo := (163933954273029736873/50000000000000000000)
  directionHi := (327867908546059473747/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree044.table
  base := (-1591904867289690426250521504480768759219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-176587778829638149054733170110758900000000000)
      constant := (1915047313944086107749660205993339355774413962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree044.table
  base := (-6368411255651909920990473917715789276439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-354047483352560611906265563304487800000000000)
      constant := (3849342623772992754137560121819868633591045761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163933954273029736873/50000000000000000000)
  centralHi := (327867908546059473747/100000000000000000000)
  directionLo := (82914603729478850989/25000000000000000000)
  directionHi := (331658414917915403957/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree045.table
  base := (-123107653876196131004726758456582415057/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-180600618668048911415002321799427650000000000)
      constant := (2005647959415369331913970425330352178975088575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree045.table
  base := (-3078033316453113505469746774600198782901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-181046489761205662788365560875946400000000000)
      constant := (2015715089721208816482341823325614684715626899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/25000000000000000000)
  centralHi := (331658414917915403957/100000000000000000000)
  directionLo := (83851521645913291021/25000000000000000000)
  directionHi := (67081217316730632817/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree046.table
  base := (-5915557202588114087597627661666749669363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-369226917012919347550542946976192800000000000)
      constant := (4196801414874210922156720422019286111622828037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree046.table
  base := (-5916147874095134243112054886378848544937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-370138475692262039247196680199297800000000000)
      constant := (4217841681553250943085401922455735965993097663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83851521645913291021/25000000000000000000)
  centralHi := (67081217316730632817/20000000000000000000)
  directionLo := (169556171849374119961/50000000000000000000)
  directionHi := (339112343698748239923/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree047.table
  base := (-176509174253627911087205925872624902977/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-188626298344870436135540625176765150000000000)
      constant := (2193304789972829898966117075307226263210705968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree047.table
  base := (-2824401803549717392697140478149698367777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-189091985931056376458831119323351400000000000)
      constant := (2204287806976240305692054304117234589450306823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169556171849374119961/50000000000000000000)
  centralHi := (339112343698748239923/100000000000000000000)
  directionLo := (342778529637366387909/100000000000000000000)
  directionHi := (34277852963736638791/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree048.table
  base := (-5353718601276213525369389508811439049163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-385278276366562396991619553730867800000000000)
      constant := (4580719120692097216994455992270968510259488237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree048.table
  base := (-1338539731077498152566482741964260374459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-193114734015981733294063898547053900000000000)
      constant := (2301815350286313717238768840148745559840287482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342778529637366387909/100000000000000000000)
  centralHi := (34277852963736638791/10000000000000000000)
  directionLo := (346405916681357766957/100000000000000000000)
  directionHi := (173202958340678883479/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree049.table
  base := (-5031939079588330651548633282997425656441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-393303956043383921712157857108205300000000000)
      constant := (4779128947631219133875344751400438229628645359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree049.table
  base := (-251615957874932958872864597328550806297/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-197137482100907090129296677770756400000000000)
      constant := (2401502933462143377812490240348740044749643030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346405916681357766957/100000000000000000000)
  centralHi := (173202958340678883479/50000000000000000000)
  directionLo := (349995711178506716433/100000000000000000000)
  directionHi := (174997855589253358217/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree050.table
  base := (-936609003343954100752310604841908195061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-401329635720205446432696160485542800000000000)
      constant := (4981838142615213156350511027618766597510913695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree050.table
  base := (-4683373038030524506130453720307102686301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-402320460371664893929058913988917800000000000)
      constant := (5006700207858803291540964531100377245497043499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349995711178506716433/100000000000000000000)
  centralHi := (174997855589253358217/50000000000000000000)
  directionLo := (353549058229329191593/100000000000000000000)
  directionHi := (176774529114664595797/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree051.table
  base := (-1682465740409881958174163401599281237/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-204677657698513485576617231931440150000000000)
      constant := (2594422965781926552699931632772392471464744640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree051.table
  base := (-2153697672120960139910154193284095482619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-205182978270757803799762236218161400000000000)
      constant := (2607356480281184061360875198609777804481803581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353549058229329191593/100000000000000000000)
  centralHi := (176774529114664595797/50000000000000000000)
  directionLo := (178533522977018601317/50000000000000000000)
  directionHi := (71413409190807440527/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree052.table
  base := (-1952102458581566023702583781847778484299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-208690497536924247936886383620108900000000000)
      constant := (2700075830799499078113312096791906311681665901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree052.table
  base := (-3904449120616451435230492680087752177223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-418411452711366321269990030883727800000000000)
      constant := (5427043481918203995208024280723999040040148177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178533522977018601317/50000000000000000000)
  centralHi := (71413409190807440527/20000000000000000000)
  directionLo := (72110141876948051809/20000000000000000000)
  directionHi := (180275354692370129523/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree053.table
  base := (-868594220670840127697167053359572059027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-212703337375335010297155535308777650000000000)
      constant := (2807877390929131098123440255419848370226731146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree053.table
  base := (-868646884790296641469520114523974995553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-213228474440608517470227794665566400000000000)
      constant := (2821845614759333401138659255598051574640727694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72110141876948051809/20000000000000000000)
  centralHi := (180275354692370129523/50000000000000000000)
  directionLo := (364001034022344968907/100000000000000000000)
  directionHi := (91000258505586242227/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree054.table
  base := (-3017673771395897311751948375478044641383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-433432354427491545314849373994892800000000000)
      constant := (5835654827386329515638032542919131091613252017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree054.table
  base := (-754463865399008535663364751999788263419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-217251222525533874305460573889268900000000000)
      constant := (2932327872864675878809040123958517019849725562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364001034022344968907/100000000000000000000)
  centralHi := (91000258505586242227/25000000000000000000)
  directionLo := (73483791818559077849/20000000000000000000)
  directionHi := (183709479546397694623/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree055.table
  base := (-2534134067829269139767067126625549061943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-441458034104313070035387677372230300000000000)
      constant := (6059851405602524613640775815179569492769119457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree055.table
  base := (-2534290751193812585933706076728724972013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-442547941220918462281386706225942800000000000)
      constant := (6089936644307012840524042920790346401560495387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73483791818559077849/20000000000000000000)
  centralHi := (183709479546397694623/50000000000000000000)
  directionLo := (370805380533144588443/100000000000000000000)
  directionHi := (92701345133286147111/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree056.table
  base := (-505947569171478131384320364455784964111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-224741856890567297377962990374783900000000000)
      constant := (3144172092463188967602703201528204575162207378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree056.table
  base := (-2023925374995525333287057885338503641521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-450593437390769175951852264673347800000000000)
      constant := (6319533599155864774928572952125069524352844279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370805380533144588443/100000000000000000000)
  centralHi := (92701345133286147111/25000000000000000000)
  directionLo := (3741611537343595959/1000000000000000000)
  directionHi := (374161153734359595901/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree057.table
  base := (-297333972111127724162427213888285981081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-457509393457956119476464284126905300000000000)
      constant := (6521132885212010816772927201061169442284963595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree057.table
  base := (-1486786330386289450276046080052449758881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-458638933560619889622317823120752800000000000)
      constant := (6553446334875581981645866956598072785009654919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/1000000000000000000)
  centralHi := (374161153734359595901/100000000000000000000)
  directionLo := (9437177401616305973/2500000000000000000)
  directionHi := (377487096064652238921/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree058.table
  base := (-184559205781763583794877363436489447437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-465535073134777644197002587504242800000000000)
      constant := (6758217269699616008940340716709833980733475815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree058.table
  base := (-184579284882957201916209076175957413933/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-466684429730470603292783381568157800000000000)
      constant := (6791674618811460865053512431690542092102347335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9437177401616305973/2500000000000000000)
  centralHi := (377487096064652238921/100000000000000000000)
  directionLo := (2974874915581454799/781250000000000000)
  directionHi := (380783989194426214273/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree059.table
  base := (-332188402278865441672885062571148049937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-473560752811599168917540890881580300000000000)
      constant := (6999597138240132145071807017263486687492592663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree059.table
  base := (-332274929577443205192675778981839267003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-474729925900321316963248940015562800000000000)
      constant := (7034218254364765361144611062872640782637302397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2974874915581454799/781250000000000000)
  centralHi := (380783989194426214273/100000000000000000000)
  directionLo := (96013145310394155677/25000000000000000000)
  directionHi := (384052581241576622709/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree060.table
  base := (142568214180848203175874982065058079863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-240793216244210346819039597129458900000000000)
      constant := (3622636160794524262058283522977110657472682463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree060.table
  base := (285061864093378423948627641788974118331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-482775422070172030633714498462967800000000000)
      constant := (7281077075360875360061431471853990324981094531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96013145310394155677/25000000000000000000)
  centralHi := (384052581241576622709/100000000000000000000)
  directionLo := (48411698594227770219/12500000000000000000)
  directionHi := (387293588753822161753/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree061.table
  base := (929164430283230324326119159743396448591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-489612112165242218358617497636255300000000000)
      constant := (7495242676598490115969431358530519605922076791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree061.table
  base := (464550092016584267879273757028865467051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-245410459120011372152090028455186400000000000)
      constant := (3766125470652930145902185768584999569129387251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/12500000000000000000)
  centralHi := (387293588753822161753/100000000000000000000)
  directionLo := (15620307941718006277/4000000000000000000)
  directionHi := (195253849271475078463/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree062.table
  base := (99992733231705755397547694910381689271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-248818895921031871539577900506796400000000000)
      constant := (3874754041082222505541050789797404741398027768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree062.table
  base := (399957095833843978810645434103212285763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-249433207204936728987322807678888900000000000)
      constant := (3893869866694813213714636171442083837054136726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15620307941718006277/4000000000000000000)
  centralHi := (195253849271475078463/50000000000000000000)
  directionLo := (393695569384275072999/100000000000000000000)
  directionHi := (393695569384275073/100000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree063.table
  base := (229728428677791269613434080008998100093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-252831735759442633899847052195465150000000000)
      constant := (4004034217904568234861551854596433057470243465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree063.table
  base := (459447322094909536674166263275683060831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-506911910579724171645111173805182800000000000)
      constant := (8047543351116762622117149889374249139517685155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393695569384275072999/100000000000000000000)
  centralHi := (393695569384275073/100000000000000000)
  directionLo := (49607229199152746233/12500000000000000000)
  directionHi := (79371566718644393973/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree064.table
  base := (1510678796464024332828254967575440842547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-256844575597853396260116203884133900000000000)
      constant := (4135461825398939040635724132918473072034821947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree064.table
  base := (604263306158127417127474637267607846623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-514957406749574885315576732252587800000000000)
      constant := (8311661709465401738925289255427488738217006115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49607229199152746233/12500000000000000000)
  centralHi := (79371566718644393973/20000000000000000000)
  directionLo := (199997549244860980819/50000000000000000000)
  directionHi := (399995098489721961639/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree065.table
  base := (943024113089625485817382676692262324039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-260857415436264158620385355572802650000000000)
      constant := (4269036826852960113201087322827019520310043678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree065.table
  base := (3772061091535361891759738532321876496641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-523002902919425598986042290699992800000000000)
      constant := (8580094736490458550822578976672580087142234841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/50000000000000000000)
  centralHi := (399995098489721961639/100000000000000000000)
  directionLo := (25194246735001581103/6250000000000000000)
  directionHi := (403107947760025297649/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree066.table
  base := (4549494770673061406243907410536383132157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-529740510549349841961309014522942800000000000)
      constant := (8809518382364327155452319262963477769331133557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree066.table
  base := (2274732161798560796419941511374790522561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-265524199544638156328253924573698900000000000)
      constant := (4426421185650512810508875051441536038120644761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25194246735001581103/6250000000000000000)
  centralHi := (403107947760025297649/100000000000000000000)
  directionLo := (406196942724580580331/100000000000000000000)
  directionHi := (101549235681145145083/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree067.table
  base := (5353547386824375992242627210333766049461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-537766190226171366681847317900280300000000000)
      constant := (9085257784125254840234982249824011216220551661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree067.table
  base := (2676760587061137991591896317860734790961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-269546947629563513163486703797401400000000000)
      constant := (4564952281176471482886258998510783018102593161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406196942724580580331/100000000000000000000)
  centralHi := (101549235681145145083/25000000000000000000)
  directionLo := (409262623519779910671/100000000000000000000)
  directionHi := (25578913969986244417/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree068.table
  base := (6184249929455823675403457288194278315919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-545791869902992891402385621277617800000000000)
      constant := (9365291814396494379464342969259558833100689719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree068.table
  base := (6184227365173077121171857775879372725291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-547139391428977739997438966042207800000000000)
      constant := (9411281266006967618334421021605813281170693491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409262623519779910671/100000000000000000000)
  centralHi := (25578913969986244417/6250000000000000000)
  directionLo := (206152755100307852147/50000000000000000000)
  directionHi := (82461102040123140859/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree069.table
  base := (1760399673876264967707914300003756803493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-276908774789907208061461962327477650000000000)
      constant := (4824810217701553398014945086999913505679864186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree069.table
  base := (3520789637167877853914467906198676198923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-277592443799414226833952262244806400000000000)
      constant := (4848486222655428359042306873329379208405213523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/50000000000000000000)
  centralHi := (82461102040123140859/20000000000000000000)
  directionLo := (415326103770623756171/100000000000000000000)
  directionHi := (103831525942655939043/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree070.table
  base := (792559054758969970480179852302231188457/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-280921614628317970421731114016146400000000000)
      constant := (4969121807570327190917375384352050614267249285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree070.table
  base := (792557383384074886558735220369295772143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-281615191884339583669185041468508900000000000)
      constant := (4993489034485146477054514162090859430858153715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415326103770623756171/100000000000000000000)
  centralHi := (103831525942655939043/25000000000000000000)
  directionLo := (209162443572444336607/50000000000000000000)
  directionHi := (83664977428977734643/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree071.table
  base := (8836222827245267991518460160875118380213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-569868908933457465564000531409630300000000000)
      constant := (10231161326490141025508625662768606801346552813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree071.table
  base := (1104526055662657711355597341258558299647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-285637939969264940504417820692211400000000000)
      constant := (5140649055239566315798008702002779075358796188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209162443572444336607/50000000000000000000)
  centralHi := (83664977428977734643/20000000000000000000)
  directionLo := (84260465210270648443/20000000000000000000)
  directionHi := (52662790756419155277/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree072.table
  base := (9773493281547271152993032860128151326037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-577894588610278990284538834786967800000000000)
      constant := (10528373546469483968062453053198948271676903437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree072.table
  base := (1221685113454163859106912976863192780217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-289660688054190297339650599915913900000000000)
      constant := (5289966273692059018396330971068596318203974468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84260465210270648443/20000000000000000000)
  centralHi := (52662790756419155277/12500000000000000000)
  directionLo := (53032358734399378739/12500000000000000000)
  directionHi := (424258869875195029913/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree073.table
  base := (2147480000207459266759275615150369072939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-585920268287100515005077138164305300000000000)
      constant := (10829880255600297939958000297697279043315253695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree073.table
  base := (5368694678052152645562400196508056177637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-293683436139115654174883379139616400000000000)
      constant := (5441440680331556003839400674192319393568075037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/12500000000000000000)
  centralHi := (424258869875195029913/100000000000000000000)
  directionLo := (26699684528162806211/6250000000000000000)
  directionHi := (427194952450604899377/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree074.table
  base := (1172794136719935233556981631637745245531/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-296972973981961019862807720770821400000000000)
      constant := (5567840718686050657490405253386073258748308655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree074.table
  base := (11727932210779924806713380898716094482227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-595412368448082022020232316726637800000000000)
      constant := (11190144534199204544517109829690353279813197627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26699684528162806211/6250000000000000000)
  centralHi := (427194952450604899377/100000000000000000000)
  directionLo := (43011099280391740877/10000000000000000000)
  directionHi := (430110992803917408771/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree075.table
  base := (1274511600800719846922496545653519650959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-300985813820371782223076872459490150000000000)
      constant := (5722888538894427205930746547180816754172163795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree075.table
  base := (6372554066455229499142152408238114206483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-301728932308966367845348937587021400000000000)
      constant := (5750861027167904925649765648027711065520333083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43011099280391740877/10000000000000000000)
  centralHi := (430110992803917408771/100000000000000000000)
  directionLo := (54125924481462151087/12500000000000000000)
  directionHi := (433007395851697208697/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree076.table
  base := (3447230690073622558688089762601529247593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-304998653658782544583346024148158900000000000)
      constant := (5880083582492548675177725746625970399709392386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree076.table
  base := (6894457994013065457685815377031148063781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-305751680393891724680581716810723900000000000)
      constant := (5908806954750100866677181339668832041398629981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54125924481462151087/12500000000000000000)
  centralHi := (433007395851697208697/100000000000000000000)
  directionLo := (435884553057074181431/100000000000000000000)
  directionHi := (54485569132134272679/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree077.table
  base := (7429680318947086361424653711716215486531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-309011493497193306943615175836827650000000000)
      constant := (6039425844450470001666444483036452223553102731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree077.table
  base := (3714838703675792930092627246351185845863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-309774428478817081515814496034426400000000000)
      constant := (6068910044942448162384598453740721806127296926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435884553057074181431/100000000000000000000)
  centralHi := (54485569132134272679/12500000000000000000)
  directionLo := (87748568609467865027/20000000000000000000)
  directionHi := (27421427690458707821/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree078.table
  base := (3989107201164376692946605609002871157877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-313024333335604069303884327525496400000000000)
      constant := (6200915320503414541302502012206218889863006554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree078.table
  base := (1595642379812431687387591360596059821599/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-313797176563742438351047275258128900000000000)
      constant := (6231170293588971354988781655617258931200656995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87748568609467865027/20000000000000000000)
  centralHi := (27421427690458707821/6250000000000000000)
  directionLo := (110395658048889976843/25000000000000000000)
  directionHi := (441582632195559907373/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree079.table
  base := (8540063275800652724026505243443376138837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-317037173174014831664153479214165150000000000)
      constant := (6364552007035213549131527041422061489367276237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree079.table
  base := (3416024449538761785269809393224344499893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-635639849297335590372560108963662800000000000)
      constant := (12791175394334573567236716615773234216217042465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110395658048889976843/25000000000000000000)
  centralHi := (441582632195559907373/100000000000000000000)
  directionLo := (444404275168743233061/100000000000000000000)
  directionHi := (222202137584371616531/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree080.table
  base := (9115226638774242586017808435953552294871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-321050013012425594024422630902833900000000000)
      constant := (6530335900979563310355701144965457186959979071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree080.table
  base := (3646089915616395280515159734843035501459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-643685345467186304043025667411067800000000000)
      constant := (13124324505383840917827997680992137025751916295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444404275168743233061/100000000000000000000)
  centralHi := (222202137584371616531/50000000000000000000)
  directionLo := (223604057722435442723/50000000000000000000)
  directionHi := (447208115444870885447/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree081.table
  base := (4851852118181333049957681285854208036989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-325062852850836356384691782591502650000000000)
      constant := (6698266999736362998024244437195138036745649578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree081.table
  base := (1940740529317141722852092067586650297091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-325865420818518508856745612929236400000000000)
      constant := (6730893957632425571597086470744276210903126455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/50000000000000000000)
  centralHi := (447208115444870885447/100000000000000000000)
  directionLo := (449994485800937206843/100000000000000000000)
  directionHi := (112498621450234301711/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree082.table
  base := (10305495852430917222682065402727686574487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-329075692689247118744960934280171400000000000)
      constant := (6868345301100819415492135438079457193246341887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree082.table
  base := (2061098897245860498016513301238828579177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-329888168903443865691978392152938900000000000)
      constant := (6901782809844023885141910861201955051680922885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449994485800937206843/100000000000000000000)
  centralHi := (112498621450234301711/25000000000000000000)
  directionLo := (452763708773955059281/100000000000000000000)
  directionHi := (226381854386977529641/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree083.table
  base := (5460300651852863005284331059091606156887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-333088532527657881105230085968840150000000000)
      constant := (7040570803203361936063187999293156683187808574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree083.table
  base := (5460300064883438682395494407095580934733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-333910916988369222527211171376641400000000000)
      constant := (7074828807508847291523583112557546504730422666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452763708773955059281/100000000000000000000)
  centralHi := (226381854386977529641/50000000000000000000)
  directionLo := (455516097096736748897/100000000000000000000)
  directionHi := (227758048548368374449/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree084.table
  base := (5774510217391457949345817094457174043193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-337101372366068643465499237657508900000000000)
      constant := (7214943504458712554599025348320268764829223586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree084.table
  base := (5774509713080011608508170115895961071143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-337933665073294579362443950600343900000000000)
      constant := (7250031949086152970114114107716670097773459486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455516097096736748897/100000000000000000000)
  centralHi := (227758048548368374449/50000000000000000000)
  directionLo := (458251954110116821949/100000000000000000000)
  directionHi := (9165039082202336439/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree085.table
  base := (4876301245557984406296595843051747114803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-682228424408958811651536778692355300000000000)
      constant := (14782926807045421479372838714388821080340527015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree085.table
  base := (24381504494802500221786193123073556768663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-683912826316439872395353459648092800000000000)
      constant := (14854784466540273032155479268682079977597131263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458251954110116821949/100000000000000000000)
  centralHi := (9165039082202336439/2000000000000000000)
  directionLo := (460971574153154833913/100000000000000000000)
  directionHi := (230485787076577416957/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree086.table
  base := (5138319691729030256862638671394411544493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-690254104085780336372075082069692800000000000)
      constant := (15140260998511416115400243641972590585826865465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree086.table
  base := (25691596970018352732631230573636373168849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-691958322486290586065819018095497800000000000)
      constant := (15213819317908358709791404066237485242695428649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460971574153154833913/100000000000000000000)
  centralHi := (230485787076577416957/50000000000000000000)
  directionLo := (46367524293273890277/10000000000000000000)
  directionHi := (463675242932738902771/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree087.table
  base := (5405663474540802410571789688134553019627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-698279783762601861092613385447030300000000000)
      constant := (15501889581383059013242009848334065595516075135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree087.table
  base := (27028316094115894103837825394512131248079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-700003818656141299736284576542902800000000000)
      constant := (15577168450401091680826294210440381575861653879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46367524293273890277/10000000000000000000)
  centralHi := (463675242932738902771/100000000000000000000)
  directionLo := (466363237873903767959/100000000000000000000)
  directionHi := (11659080946847594199/2500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree088.table
  base := (14195831404694776552145108665957947573201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-353152731719711692906575844412183900000000000)
      constant := (7933906277011152346686019113337386523194223401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree088.table
  base := (28391661711318398906141486190732090132217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-708049314825992013406750134990307800000000000)
      constant := (15944831862429393569156222624570692851438745617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466363237873903767959/100000000000000000000)
  centralHi := (11659080946847594199/2500000000000000000)
  directionLo := (469035828452079193543/100000000000000000000)
  directionHi := (58629478556509899193/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree089.table
  base := (29781634632598793986758874401780893469091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-714331143116244910533689992201705300000000000)
      constant := (16238029915040766652201026047454094363028197291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree089.table
  base := (29781633689654869809635327414073968773403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-716094810995842727077215693437712800000000000)
      constant := (16316809552647028231018809169151003580457484003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469035828452079193543/100000000000000000000)
  centralHi := (58629478556509899193/12500000000000000000)
  directionLo := (235846638254197495569/50000000000000000000)
  directionHi := (471693276508394991139/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree090.table
  base := (31198232726990654158161081399654603158627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-722356822793066435254228295579042800000000000)
      constant := (16612541663261850527118972056677524731821154027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree090.table
  base := (31198231917340524760886911922302806896911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-724140307165693440747681251885117800000000000)
      constant := (16693101519913679104686989552893374933155389111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235846638254197495569/50000000000000000000)
  centralHi := (471693276508394991139/100000000000000000000)
  directionLo := (94867167309817380479/20000000000000000000)
  directionHi := (118583959137271725599/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree091.table
  base := (16320728497418623803584605447518307571847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-365191251234943979987383299478190150000000000)
      constant := (8495673898844317076462161563463264739915411247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree091.table
  base := (32641456299707899353902979844883277502193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-732185803335544154418146810332522800000000000)
      constant := (17073707763263643385755226531858476038799870793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94867167309817380479/20000000000000000000)
  centralHi := (118583959137271725599/25000000000000000000)
  directionLo := (476963756029972363493/100000000000000000000)
  directionHi := (238481878014986181747/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree092.table
  base := (17055653676676423104288634346149456083313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-369204091073354742347652451166858900000000000)
      constant := (8687224158738310158505926455705753601505875913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree092.table
  base := (34111306756604613737235138953030864978521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-740231299505394868088612368779927800000000000)
      constant := (17458628281879286647358895056920476053645892721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476963756029972363493/100000000000000000000)
  centralHi := (238481878014986181747/50000000000000000000)
  directionLo := (239788637813448069871/50000000000000000000)
  directionHi := (479577275626896139743/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree093.table
  base := (17803891866213947713453977398456423587921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-373216930911765504707921602855527650000000000)
      constant := (8880921610955310726782578736444135586395382121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree093.table
  base := (4450972902523337019268832708454862950029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-374138397837622790879538963613666400000000000)
      constant := (8923931537534266266803782287022453940312983316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/50000000000000000000)
  centralHi := (479577275626896139743/100000000000000000000)
  directionLo := (241088314746491198679/50000000000000000000)
  directionHi := (482176629492982397359/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree094.table
  base := (37130886072706540727984658820608897131667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-754459541500352534136381509088392800000000000)
      constant := (18153532510385148490481101208786083984640135067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree094.table
  base := (232068035206545152877643078154593921701/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-378161145922548147714771742837368900000000000)
      constant := (9120706071122886515853989485319884707621752080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241088314746491198679/50000000000000000000)
  centralHi := (482176629492982397359/100000000000000000000)
  directionLo := (121190511375867864997/25000000000000000000)
  directionHi := (484762045503471459989/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree095.table
  base := (38680614323955501514495019366058524532443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-762485221177174058856919812465730300000000000)
      constant := (18549516182387771732386500720490797227505451043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree095.table
  base := (19340306973314623865558531791605808392521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-382183894007473504550004522061071400000000000)
      constant := (9319637741457839342637439339774940913912106721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121190511375867864997/25000000000000000000)
  centralHi := (484762045503471459989/100000000000000000000)
  directionLo := (487333745488865819427/100000000000000000000)
  directionHi := (121833436372216454857/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree096.table
  base := (10064242110920018209370053810663615592049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-385255450426997791788729057921533900000000000)
      constant := (9474897118742501347048513536518513085308983698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree096.table
  base := (20128484059939869943129605847208400869037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-386206642092398861385237301284773900000000000)
      constant := (9520726548329733787633224651041893697265046437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487333745488865819427/100000000000000000000)
  centralHi := (121833436372216454857/25000000000000000000)
  directionLo := (244945972728530259497/50000000000000000000)
  directionHi := (97978389091412103799/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree097.table
  base := (8371989679189952858325864897625151228893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-778536580530817108297996419220405300000000000)
      constant := (19354366675310314442988103551487644807179687465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree097.table
  base := (8371989623621586727531196257801110476123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-780458780354648436440940161016952800000000000)
      constant := (19447944983123259184575830418282617464834653615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/50000000000000000000)
  centralHi := (97978389091412103799/20000000000000000000)
  directionLo := (7694325871954491107/1562500000000000000)
  directionHi := (492436855805087430849/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree098.table
  base := (43489554150401786933228657026637843093041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-786562260207638633018534722597742800000000000)
      constant := (19763233495553976169044906803379064762392111241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree098.table
  base := (10872388478004242433614570218108025443809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-394252138262249575055702859732178900000000000)
      constant := (9929375571004098125992555222905255335104591218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7694325871954491107/1562500000000000000)
  centralHi := (492436855805087430849/100000000000000000000)
  directionLo := (494968681521060868231/100000000000000000000)
  directionHi := (61871085190132608529/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree099.table
  base := (361166285451163443796348919580458560613/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-794587939884460157739073025975080300000000000)
      constant := (20176394697954426986622256195424914690851651625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree099.table
  base := (45145785476882528741463544598299835609651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-796549772694349863781871277911762800000000000)
      constant := (20273871573062065994935788010468375148054049851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494968681521060868231/100000000000000000000)
  centralHi := (61871085190132608529/12500000000000000000)
  directionLo := (99497524475374621187/20000000000000000000)
  directionHi := (31092976398554569121/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree100.table
  base := (46828642967294467766816750179523118262943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-802613619561281682459611329352417800000000000)
      constant := (20593850282290955742575676999849240329400281543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree100.table
  base := (5853580348982015209464524175977798657233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-402297634432100288726168418179583900000000000)
      constant := (10346653138036096488656366625138765596409735332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99497524475374621187/20000000000000000000)
  centralHi := (31092976398554569121/6250000000000000000)
  directionLo := (31249617069509528253/6250000000000000000)
  directionHi := (499993873112152452049/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree101.table
  base := (24269062994929097242331792321531811467961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (62)
      previous := (31)
      next := (31)
      square := (392405802558197028262476635000000000000)
      linear := (-39733325126855367472804118847650000000000)
      constant := (1030075494969977894916278901860766186467961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree101.table
  base := (48538125839374112729128486796231567769303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (124)
      previous := (62)
      next := (62)
      square := (784811605116394056524953270000000000000)
      linear := (-79662853154989833459739476012800000000000)
      constant := (2070096583752515493602356937981456567769303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31249617069509528253/6250000000000000000)
  centralHi := (499993873112152452049/100000000000000000000)
  directionLo := (50248762360996327211/10000000000000000000)
  directionHi := (502487623609963272111/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree102.table
  base := (50274234733724654398761193560066687234987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-818664978914924731900687936107092800000000000)
      constant := (21441644596057319479645668507505726901484102387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree102.table
  base := (12568558651164106467571138716761751245233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-410343130601951002396633976626988900000000000)
      constant := (10772559248636473579057022171934150348905243666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50248762360996327211/10000000000000000000)
  centralHi := (502487623609963272111/100000000000000000000)
  directionLo := (504969059064696587553/100000000000000000000)
  directionHi := (252484529532348293777/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree103.table
  base := (10407393837194419085626093454094554302513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-826690658591746256621226239484430300000000000)
      constant := (21871983325198632352288848157434098460949675565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree103.table
  base := (52036969075281326737503471083862332686217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-828731757373752718463733511701382800000000000)
      constant := (21977496015186088688718429777238036580732099617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504969059064696587553/100000000000000000000)
  centralHi := (252484529532348293777/50000000000000000000)
  directionLo := (63429795017821418611/12500000000000000000)
  directionHi := (507438360142571348889/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree104.table
  base := (6728291166968352143983230178291653238231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-417358169134283890670882271430883900000000000)
      constant := (11153308217845354516008901721817521118732777724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree104.table
  base := (26913164620412369539341641915567974786453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-418388626771801716067099535074393900000000000)
      constant := (11207093902246249570101553708013953110796607053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63429795017821418611/12500000000000000000)
  centralHi := (507438360142571348889/100000000000000000000)
  directionLo := (254947851567570017351/50000000000000000000)
  directionHi := (509895703135140034703/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree105.table
  base := (6955289396743420562601094170039505205311/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-421371008972694653031151423119552650000000000)
      constant := (11372771963720352787836023934169552204772510044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree105.table
  base := (13910578773138576976457637221157168875653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-422411374856727072902332314298096400000000000)
      constant := (11427596932551549879667778067853222871901072506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254947851567570017351/50000000000000000000)
  centralHi := (509895703135140034703/100000000000000000000)
  directionLo := (128085315026541920289/25000000000000000000)
  directionHi := (512341260106167681157/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree106.table
  base := (7185615836619567992844577122649668292257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-425383848811105415391420574808221400000000000)
      constant := (11594382900185459496014791425414855127497254628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree106.table
  base := (28742463311584953814146927850958257778021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-426434122941652429737565093521798900000000000)
      constant := (11650257098471710982482770448665193987593592221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128085315026541920289/25000000000000000000)
  centralHi := (512341260106167681157/100000000000000000000)
  directionLo := (514775199032230649623/100000000000000000000)
  directionHi := (64346899879028831203/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree107.table
  base := (7419270485801753639973273178291827508737/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-429396688649516177751689726496890150000000000)
      constant := (11818141027208233795956616674930521714041504548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree107.table
  base := (11870832765316710688388637580776219454029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-860913742053155573145595745491002800000000000)
      constant := (23750148799951362224106131403816346398252749145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514775199032230649623/100000000000000000000)
  centralHi := (64346899879028831203/12500000000000000000)
  directionLo := (517197683937360252383/100000000000000000000)
  directionHi := (16162427623042507887/3125000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree108.table
  base := (61250026749023417746153112191222417654037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-866819056975853880223917756371117800000000000)
      constant := (24088092689523322775606121286740643882488831437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree108.table
  base := (15312506674433185668077829359182502837061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-434479619111503143408030651969203900000000000)
      constant := (12102048837037638973487543730893792322881718522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517197683937360252383/100000000000000000000)
  centralHi := (16162427623042507887/3125000000000000000)
  directionLo := (103921775004407330087/20000000000000000000)
  directionHi := (129902218755509162609/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree109.table
  base := (7896564409548566301517929076451416297953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-437422368326337702472228029874227650000000000)
      constant := (12272098852823319558474877253964251699996674212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree109.table
  base := (63172515232422158807226907372508894529487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-877004734392857000486526862385812800000000000)
      constant := (24662360819272372709831749263242040258095296887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103921775004407330087/20000000000000000000)
  centralHi := (129902218755509162609/25000000000000000000)
  directionLo := (130502232196705024251/25000000000000000000)
  directionHi := (104401785757364019401/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree110.table
  base := (6512162946487452999907515711138177006551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-441435208164748464832497181562896400000000000)
      constant := (12502298551374668821248229018879313030719133755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree110.table
  base := (13024325885437887869846760439947448106657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-885050230562707714156992420833217800000000000)
      constant := (25124938235507326952839566565807100590680040285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130502232196705024251/25000000000000000000)
  centralHi := (104401785757364019401/20000000000000000000)
  directionLo := (524397998150889519029/100000000000000000000)
  directionHi := (52439799815088951903/10000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree111.table
  base := (67097369311490109080209298593616533964031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-890896096006318454385532666503130300000000000)
      constant := (25469290880800904025186067468855359481717080231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree111.table
  base := (13419473855838272065744652936298789381129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-893095726732558427827457979280622800000000000)
      constant := (25591829922751136948284560640928933477384484645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524397998150889519029/100000000000000000000)
  centralHi := (52439799815088951903/10000000000000000000)
  directionLo := (263388116282871254889/50000000000000000000)
  directionHi := (526776232565742509779/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree112.table
  base := (17274933703446890022265287307576322218653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-449460887841569989553035484940233900000000000)
      constant := (12969139519888184600066436148332585125904958506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree112.table
  base := (17274933696526835775634109082705411206851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-450570611451204570748961768864013900000000000)
      constant := (13031517940490065236713933986591043399442174102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263388116282871254889/50000000000000000000)
  centralHi := (526776232565742509779/100000000000000000000)
  directionLo := (529143778124295959819/100000000000000000000)
  directionHi := (26457188906214797991/5000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree113.table
  base := (1778218149244450613683605888409974775781/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-453473727679980751913304636628902650000000000)
      constant := (13205780789827722410999936102583536538129839620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree113.table
  base := (17782181486514414491711000991607469433183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-454593359536129927584194548087716400000000000)
      constant := (13269278055087566202780362869402108303875799566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529143778124295959819/100000000000000000000)
  centralHi := (26457188906214797991/5000000000000000000)
  directionLo := (132875194416403174933/25000000000000000000)
  directionHi := (531500777665612699733/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree114.table
  base := (73184342777859626287839451196281989005449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-914973135036783028547147576635142800000000000)
      constant := (26889138500421790152005265090835472694844585249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree114.table
  base := (73184342757534096889367157767840948873779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-917232215242110568838854654622837800000000000)
      constant := (27018390610320757514545857798816629919461419579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132875194416403174933/25000000000000000000)
  centralHi := (531500777665612699733/100000000000000000000)
  directionLo := (533847370875466591623/100000000000000000000)
  directionHi := (66730921359433323953/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree115.table
  base := (1176040394324320944216272082224018427321/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-461499407356802276633842940006240150000000000)
      constant := (13685504901031195250270487671110863517642248672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree115.table
  base := (147005049256525830317876884175694597481/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-462638855705980641254660106535121400000000000)
      constant := (13751269690702405585262758441653938773259342336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533847370875466591623/100000000000000000000)
  centralHi := (66730921359433323953/12500000000000000000)
  directionLo := (536183694382946419487/100000000000000000000)
  directionHi := (16755740449467075609/3125000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree116.table
  base := (77375453345467344234524544335911120845643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-931024494390426077988224183389817800000000000)
      constant := (27857175484567030354248243244282172343746404243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree116.table
  base := (77375453330546607760029503680480440000561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-933323207581811996179785771517647800000000000)
      constant := (27991002423417781605013682425378689568445722761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536183694382946419487/100000000000000000000)
  centralHi := (16755740449467075609/3125000000000000000)
  directionLo := (16828433807915238377/3125000000000000000)
  directionHi := (107701976370657525613/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree117.table
  base := (39755473551610622914847299433547293468651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-469525087033623801354381243383577650000000000)
      constant := (14173817773963923432619407649081092300048708851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree117.table
  base := (79510947090438650201614999236672082875739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-941368703751662709850251329965052800000000000)
      constant := (28483779736352409841500020733370405742415413539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828433807915238377/3125000000000000000)
  centralHi := (107701976370657525613/20000000000000000000)
  directionLo := (540826064077110388567/100000000000000000000)
  directionHi := (67603258009638798571/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree118.table
  base := (16334613301888199777385947939838386532899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-947075853744069127429300790144492800000000000)
      constant := (28842389992138951543716460343026311530110513495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree118.table
  base := (8167306649849089760661406011490033948601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-474707099960756711760358444206228900000000000)
      constant := (14490435660101662757076278960562573081548394005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540826064077110388567/100000000000000000000)
  centralHi := (67603258009638798571/12500000000000000000)
  directionLo := (543132369056232574637/100000000000000000000)
  directionHi := (271566184528116287319/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree119.table
  base := (81896300355187003296456583098349357761/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-477550766710445326074919546760915150000000000)
      constant := (14670719408598054915928215888952990400217220032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree119.table
  base := (41930905777165906641458125895491558646333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-478729848045682068595591223429931400000000000)
      constant := (14741138587483369288587537723030864652251242933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543132369056232574637/100000000000000000000)
  centralHi := (271566184528116287319/50000000000000000000)
  directionLo := (545428922086216964507/100000000000000000000)
  directionHi := (136357230521554241127/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree120.table
  base := (10759647783219143669624233311635973268089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-481563606548856088435188698449583900000000000)
      constant := (14922391011548234897955402191904061753231103556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree120.table
  base := (43038591128859602182993063057533028979417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-482752596130607425430824002653633900000000000)
      constant := (14993998650320089210578223600801745428619032817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545428922086216964507/100000000000000000000)
  centralHi := (136357230521554241127/25000000000000000000)
  directionLo := (547715845835803300883/100000000000000000000)
  directionHi := (136928961458950825221/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree121.table
  base := (88319178615399426533554173540956798480397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-971152892774533701590915700276505300000000000)
      constant := (30352419609838332497097326586124813770048529797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree121.table
  base := (22079794652129647265216695102494979160233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-486775344215532782266056781877336400000000000)
      constant := (15249015848611136598653158911770313677327073666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547715845835803300883/100000000000000000000)
  centralHi := (136928961458950825221/25000000000000000000)
  directionLo := (137498315105841924313/25000000000000000000)
  directionHi := (549993260423367697253/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree122.table
  base := (90587800612577760420721010462332271739667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-979178572451355226311454003653842800000000000)
      constant := (30864351577420957725511293045309635629016343067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree122.table
  base := (18117560121336981316328404954658104602447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-981596184600916278202579122202077800000000000)
      constant := (31012380364712563240547556258678407825247809235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137498315105841924313/25000000000000000000)
  centralHi := (549993260423367697253/100000000000000000000)
  directionLo := (552261283490544240259/100000000000000000000)
  directionHi := (27613064174527212013/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree123.table
  base := (23220762064323367382613744065244458311941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-493602126064088375515996153515590150000000000)
      constant := (15690288962922199867646606915899990922855220282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree123.table
  base := (46441524126123530803117264110551796795929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-494820840385383495936522340324741400000000000)
      constant := (15765521651555671703749825826825063341615271729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552261283490544240259/100000000000000000000)
  centralHi := (27613064174527212013/5000000000000000000)
  directionLo := (17328750946035514607/3125000000000000000)
  directionHi := (22180801210925458697/4000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree124.table
  base := (95204921549616145352908246330179217476383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-995229931804998275752530610408517800000000000)
      constant := (31901098655109368429234131286782760197476582983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree124.table
  base := (47602460772647436011209432379622462725187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-498843588470308852771755119548443900000000000)
      constant := (16027010256209764965217896218944606442259632587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17328750946035514607/3125000000000000000)
  centralHi := (22180801210925458697/4000000000000000000)
  directionLo := (278384806834719832723/50000000000000000000)
  directionHi := (556769613669439665447/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree125.table
  base := (48776710244834080167686114599509104871997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-501627805740909900236534456892927650000000000)
      constant := (16212956882608556064334432534331566988174241397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree125.table
  base := (12194177560746006756506579153289756130337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-502866336555234209606987898772146400000000000)
      constant := (16290655996319274027267573988574130521642270948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278384806834719832723/50000000000000000000)
  centralHi := (556769613669439665447/100000000000000000000)
  directionLo := (559010144306088606807/100000000000000000000)
  directionHi := (69876268038261075851/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree126.table
  base := (49964272538807485146431627090224444355719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-505640645579320662596803608581596400000000000)
      constant := (16477511628084659324183198376381273869372689519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree126.table
  base := (19985709014889386853662690958798110184861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-1013778169280319132884441355991697800000000000)
      constant := (33112917743770237291170703184999452209978835305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559010144306088606807/100000000000000000000)
  centralHi := (69876268038261075851/12500000000000000000)
  directionLo := (11224834612030787877/2000000000000000000)
  directionHi := (561241730601539393851/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree127.table
  base := (51165147656828469140336925577933757199463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-509653485417731424957072760270265150000000000)
      constant := (16744213563984015945926882718200562366566722063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree127.table
  base := (102330295310944625061380126514268039034649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-1021823665450169846554906914439102800000000000)
      constant := (33648837765816771599834671970170295591192454449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11224834612030787877/2000000000000000000)
  centralHi := (561241730601539393851/100000000000000000000)
  directionLo := (281732239413644242131/50000000000000000000)
  directionHi := (563464478827288484263/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree128.table
  base := (104758671198022448220159542361186110235003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-1027332650512284374634683823917867800000000000)
      constant := (34026125380615581603512718801907403510507265603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree128.table
  base := (10475867119570044003097801041706998869481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-514934580810010280112686236443253900000000000)
      constant := (17094536029390296109278926375363999877337878405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell063.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281732239413644242131/50000000000000000000)
  centralHi := (563464478827288484263/100000000000000000000)
  directionLo := (565678493166926706549/100000000000000000000)
  directionHi := (11313569863338534131/2000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree129.table
  base := (107213672730962111602335855012198419047947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1264924)
      previous := (632462)
      next := (632462)
      square := (8005863183792335770611048307270000000000000)
      linear := (-1035358330189105899355222127295205300000000000)
      constant := (34568118014114524271163106242409696041458107347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree129.table
  base := (53606836364487179833330843330393082324181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (632462)
      previous := (316231)
      next := (316231)
      square := (4002931591896167885305524153635000000000000)
      linear := (-518957328894935636947919015666956400000000000)
      constant := (17366810311332175604157095899434149345288970381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell063.Kernel129
