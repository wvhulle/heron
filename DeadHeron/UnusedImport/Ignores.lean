module

meta import DeadHeron.Assert
meta import DeadHeron.UnusedImport

-- The `unusedImport` rule operates at file-import scope, not at command
-- scope.  `#assertIgnore` re-elaborates a single command, so it cannot
-- meaningfully test "no unused imports".  The Detects test file covers
-- the rule's main behavior; this file is intentionally minimal.
