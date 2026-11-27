# Independent FVA proposal review

The owner supplied the following external review conclusion for proposal revision `9740a5d6bd188f3ed879249e64a2a4eab3347bf2`.

> Mandatory changes: None.
>
> RECOMMEND FREEZING FVA-B AND FVA-E AS WRITTEN at 9740a5d6bd188f3ed879249e64a2a4eab3347bf2.

The reviewer offered the following non-blocking implementation guidance. Keep square root out of the common Scalar interface. Where practical, give conserved states their own operations independently of Burgers and SSP constants. Preserve eulerStepArray and its E0 and SSPRK callers.
