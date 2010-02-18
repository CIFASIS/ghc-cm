
/* gcc on mingw is hardcoded to use /mingw (which is c:/mingw) to
   find various files. If this is a different version of mingw to the
   one that we have in the GHC tree then things can go wrong. We
   therefore need to add various -B flags to the gcc commandline,
   so that it uses our in-tree mingw. Hence this wrapper. */

#include "cwrapper.h"
#include "getLocation.h"
#include <errno.h>
#include <process.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

int main(int argc, char** argv) {
    char *binDir;
    char *exePath;
    char *preArgv[4];

    binDir = getExecutablePath();
    exePath = mkString("%s/realgcc.exe", binDir);

    /* Without these -B args, gcc will still work. However, if you
       have a mingw installation in c:/mingw then it will use files
       from that in preference to the in-tree files. */
    preArgv[0] = mkString("-B%s", binDir);
    preArgv[1] = mkString("-B%s/../lib", binDir);
    preArgv[2] = mkString("-B%s/../lib/gcc/mingw32/3.4.5", binDir);
    preArgv[3] = mkString("-B%s/../libexec/gcc/mingw32/3.4.5", binDir);

    run(exePath, 4, preArgv, argc - 1, argv + 1);
}

