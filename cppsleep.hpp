#ifndef CPPSLEEP_HPP
#define CPPSLEEP_HPP

#ifdef _WIN32
#include <windows.h>
void sleep_milliseconds(int milliseconds)
{
    Sleep(milliseconds);
}
#else
#include <unistd.h>
void sleep_milliseconds(int milliseconds)
{
    usleep(milliseconds * 1000);
}
#endif

void sleepfloat(double seconds)
{
    int milliseconds{(int)(seconds * 1000)};
    sleep_milliseconds(milliseconds);
}

#endif
