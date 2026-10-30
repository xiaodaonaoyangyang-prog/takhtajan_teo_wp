param(
  [Parameter(Mandatory=$true)][ValidatePattern('^(lean[1-6]|leader)$')][string]$Owner,
  [Parameter(Mandatory=$true)][string]$Source,
  [Parameter(Mandatory=$true)][string]$Log,
  [switch]$Publish,
  [switch]$WaitForResources
)
$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath (Split-Path -Parent $PSScriptRoot)
if (-not (Test-Path -LiteralPath $Source -PathType Leaf)) { throw "Source missing: $Source" }
Add-Type -TypeDefinition @'
using System;
using System.Runtime.InteropServices;
public class TTCompileMemory {
  [StructLayout(LayoutKind.Sequential)] public struct Status {
    public uint length, load;
    public ulong totalPhys, availPhys, totalPage, availPage, totalVirtual, availVirtual, extended;
  }
  [DllImport("kernel32.dll")] public static extern bool GlobalMemoryStatusEx(ref Status s);
  public static ulong Available() {
    Status s = new Status(); s.length = (uint)Marshal.SizeOf(s);
    if (!GlobalMemoryStatusEx(ref s)) throw new Exception("Memory query failed");
    return s.availPhys;
  }
}
'@
$ttSlotDir = Join-Path $PSScriptRoot 'lean_slots'
$ttSlot = Join-Path $ttSlotDir $Owner
$ttMutex = [Threading.Mutex]::new($false, 'Local\TakhtajanTeoLeanCompileSlots')
$ttAcquired = $false
$ttExit = 75
try {
  do {
    $ttLocked = $false
    try {
      try { $ttLocked = $ttMutex.WaitOne(5000) }
      catch [Threading.AbandonedMutexException] { $ttLocked = $true }
      if ($ttLocked) {
        $ttFree = [TTCompileMemory]::Available()
        $ttCount = @(Get-ChildItem -LiteralPath $ttSlotDir).Count
        if ($ttFree -ge 6GB -and $ttCount -lt 2 -and -not (Test-Path -LiteralPath $ttSlot)) {
          $ttHandle = [IO.File]::Open($ttSlot, [IO.FileMode]::CreateNew)
          $ttHandle.Dispose()
          $ttAcquired = $true
          Set-Content -LiteralPath $ttSlot -Value "$Owner wrapper PID $PID; $Source"
          # Also protect against an older peer not yet using this mutex.
          if (@(Get-ChildItem -LiteralPath $ttSlotDir).Count -gt 2 -or [TTCompileMemory]::Available() -lt 6GB) {
            Remove-Item -LiteralPath $ttSlot
            $ttAcquired = $false
          }
        }
      }
    } finally {
      if ($ttLocked) { $ttMutex.ReleaseMutex() }
    }
    if ($ttAcquired) { break }
    if (-not $WaitForResources) { Write-Output 'Compile deferred: no slot or insufficient RAM.'; exit 75 }
    Start-Sleep -Seconds 2
  } while ($true)
  Write-Output "Compiling $Source ($Owner; $([math]::Round($ttFree / 1GB,2)) GiB free)"
  $ttLake = 'D:/lean/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lake.exe'
  $ttLean = 'D:/lean/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean.exe'
  if ($Publish) {
    $ttStem = [IO.Path]::ChangeExtension($Source, $null).TrimEnd('.')
    & $ttLake env $ttLean -DautoImplicit=false -DrelaxedAutoImplicit=false -o ".lake/build/lib/lean/$ttStem.olean" -i ".lake/build/lib/lean/$ttStem.ilean" $Source *> $Log
  } else {
    & $ttLake env $ttLean -DautoImplicit=false -DrelaxedAutoImplicit=false $Source *> $Log
  }
  $ttExit = $LASTEXITCODE
  Get-Content -LiteralPath $Log -Tail 30
} finally {
  if ($ttAcquired) { Remove-Item -LiteralPath $ttSlot }
  $ttMutex.Dispose()
}
exit $ttExit
