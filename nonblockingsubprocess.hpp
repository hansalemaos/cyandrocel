#ifndef SHELL_PROCESS_MANAGER_H
#define SHELL_PROCESS_MANAGER_H

#define _CRT_SECURE_NO_WARNINGS

#include <iostream>
#include <istream>
#include <mutex>
#include <ostream>
#include <stdio.h>
#include <string>
#include <thread>
#include <vector>

#ifdef _WIN32
#include <windows.h>
#else
#include <fcntl.h>
#include <pthread.h>

#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

static const char* On_IRed{ "\033[0;101m" }; // Red
static const char* Color_Off{ "\033[0m" };   // Text Reset
static const char* IYellow{ "\033[0;93m" };  // Yellow

static bool isspace_or_empty(std::string& str)
    {
    if (str.size() == 0)
        {
        return true;
        }
    for (size_t i{}; i < str.size(); i++)
        {
        if (!::isspace(str[i]))
            {
            return false;
            }
        }
    return true;
    }

static void print_red(std::string& msg)
    {
    if (isspace_or_empty(msg))
        {
        return;
        }
    puts(On_IRed);
    puts(msg.c_str());
    puts(Color_Off);
    }
static void print_yellow(std::string& msg)
    {
    if (isspace_or_empty(msg))
        {
        return;
        }
    fputs(IYellow, stderr);
    fputs(msg.c_str(), stderr);
    fputs(Color_Off, stderr);
    }

void sleepcp(int milliseconds);

void sleepcp(int milliseconds)
    {
#ifdef _WIN32
    Sleep(milliseconds);
#else
    usleep(milliseconds * 1000);
#endif // _WIN32
    }
void sleepcp(int milliseconds);

#ifdef _WIN32
static std::string ws2s(std::wstring& str)
    {
    int size_needed = WideCharToMultiByte(CP_UTF8, 0, &str[0], (int)str.size(), NULL, 0, NULL, NULL);
    std::string strTo(size_needed, 0);
    WideCharToMultiByte(CP_UTF8, 0, &str[0], (int)str.size(), &strTo[0], size_needed, NULL, NULL);
    return strTo;
    }

static std::wstring s2ws(std::string& str)
    {
    int size_needed = MultiByteToWideChar(CP_UTF8, 0, &str[0], (int)str.size(), NULL, 0);
    std::wstring wstrTo(size_needed, 0);
    MultiByteToWideChar(CP_UTF8, 0, &str[0], (int)str.size(), &wstrTo[0], size_needed);
    return wstrTo;
    }
class ShellProcessManager
    {
    public:
        ShellProcessManager(std::string shell_command, size_t buffer_size = 4096, size_t stdout_max_len = 4096,
                            size_t stderr_max_len = 4096, std::string exit_command = "exit", int print_stdout = 1,
                            int print_stderr = 1)
            : shell_command(shell_command), buffer_size(buffer_size), stdout_max_len(stdout_max_len),
            stderr_max_len(stderr_max_len), exit_command(exit_command), continue_reading_stdout(true),
            continue_reading_stderr(true), siStartInfo{}, print_stdout((bool)print_stdout),
            print_stderr((bool)print_stderr)
            {
            }
        ~ShellProcessManager()
            {
            stop_shell();
            }

    private:
        std::string shell_command;
        STARTUPINFO siStartInfo;

        HANDLE g_hChildStd_IN_Rd = NULL;
        HANDLE g_hChildStd_IN_Wr = NULL;
        HANDLE g_hChildStd_OUT_Rd = NULL;
        HANDLE g_hChildStd_OUT_Wr = NULL;
        HANDLE g_hChildStd_ERR_Rd = NULL;
        HANDLE g_hChildStd_ERR_Wr = NULL;
        size_t buffer_size;
        bool continue_reading_stdout;
        bool continue_reading_stderr;
        std::vector<std::string> strmap_out;
        std::vector<std::string> strmap_err;
        std::thread t1;
        std::thread t2;
        std::mutex my_mutex_lock;
        size_t stdout_max_len;
        size_t stderr_max_len;
        std::string exit_command;
        bool print_stdout;
        bool print_stderr;

    private:
        void create_startup_info(DWORD creationFlags = 0x08000000, WORD wShowWindow = 1, LPSTR lpReserved = nullptr,
                                 LPSTR lpDesktop = nullptr, LPSTR lpTitle = nullptr, DWORD dwX = 0, DWORD dwY = 0,
                                 DWORD dwXSize = 0, DWORD dwYSize = 0, DWORD dwXCountChars = 0, DWORD dwYCountChars = 0,
                                 DWORD dwFillAttribute = 0, DWORD dwFlags = 0, WORD cbReserved2 = 0,
                                 LPBYTE lpReserved2 = nullptr)
            {
            TCHAR lpReservedarray[512]{};
            if (lpReserved != nullptr)
                {
                std::string lpReservedwstring(lpReserved);
                for (int i{}; i < lpReservedwstring.size(); i++)
                    {
                    lpReservedarray[i] = lpReservedwstring.c_str()[i];
                    }
                }
            TCHAR lpDesktoparray[512]{};
            if (lpDesktop != nullptr)
                {
                std::string lpDesktopwstring(lpDesktop);
                for (int i{}; i < lpDesktopwstring.size(); i++)
                    {
                    lpDesktoparray[i] = lpDesktopwstring.c_str()[i];
                    }
                }
            TCHAR lpTitlearray[512]{};
            if (lpTitle != nullptr)
                {
                std::string lpTitlewstring(lpTitle);
                for (int i{}; i < lpTitlewstring.size(); i++)
                    {
                    lpTitlearray[i] = lpTitlewstring.c_str()[i];
                    }
                }
            ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
            siStartInfo.lpReserved = lpReservedarray;
            siStartInfo.lpDesktop = lpDesktoparray;
            siStartInfo.lpTitle = lpTitlearray;
            siStartInfo.dwX = dwX;
            siStartInfo.dwY = dwY;
            siStartInfo.dwXSize = dwXSize;
            siStartInfo.dwYSize = dwYSize;
            siStartInfo.dwXCountChars = dwXCountChars;
            siStartInfo.dwYCountChars = dwYCountChars;
            siStartInfo.dwFillAttribute = dwFillAttribute;
            siStartInfo.dwFlags |= STARTF_USESTDHANDLES;
            siStartInfo.wShowWindow = wShowWindow;
            siStartInfo.cbReserved2 = cbReserved2;
            siStartInfo.lpReserved2 = lpReserved2;
            siStartInfo.cb = sizeof(STARTUPINFO);
            }

    public:
        bool start_shell(DWORD creationFlag = 0, DWORD creationFlags = CREATE_NO_WINDOW, WORD wShowWindow = SW_NORMAL,
                         LPSTR lpReserved = nullptr, LPSTR lpDesktop = nullptr, LPSTR lpTitle = nullptr, DWORD dwX = 0,
                         DWORD dwY = 0, DWORD dwXSize = 0, DWORD dwYSize = 0, DWORD dwXCountChars = 0,
                         DWORD dwYCountChars = 0, DWORD dwFillAttribute = 0, DWORD dwFlags = 0, WORD cbReserved2 = 0,
                         LPBYTE lpReserved2 = nullptr)
            {
            create_startup_info(creationFlags, wShowWindow, lpReserved, lpDesktop, lpTitle, dwX, dwY, dwXSize, dwYSize,
                                dwXCountChars, dwYCountChars, dwFillAttribute, dwFlags, cbReserved2, lpReserved2);
            SECURITY_ATTRIBUTES saAttr;
            saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
            saAttr.bInheritHandle = TRUE;
            saAttr.lpSecurityDescriptor = NULL;

            if (!CreatePipe(&g_hChildStd_OUT_Rd, &g_hChildStd_OUT_Wr, &saAttr, 0))
                return false;
            if (!SetHandleInformation(g_hChildStd_OUT_Rd, HANDLE_FLAG_INHERIT, 0))
                return false;
            if (!CreatePipe(&g_hChildStd_IN_Rd, &g_hChildStd_IN_Wr, &saAttr, 0))
                return false;
            if (!SetHandleInformation(g_hChildStd_IN_Wr, HANDLE_FLAG_INHERIT, 0))
                return false;
            if (!CreatePipe(&g_hChildStd_ERR_Rd, &g_hChildStd_ERR_Wr, &saAttr, 0))
                return false;
            if (!SetHandleInformation(g_hChildStd_ERR_Rd, HANDLE_FLAG_INHERIT, 0))
                return false;

            siStartInfo.hStdError = g_hChildStd_ERR_Wr;
            siStartInfo.hStdOutput = g_hChildStd_OUT_Wr;
            siStartInfo.hStdInput = g_hChildStd_IN_Rd;

            std::wstring mycmd{ s2ws(shell_command) };
            TCHAR mychararray[1024]{};
            for (int i{}; i < mycmd.size(); i++)
                {
                mychararray[i] = mycmd.c_str()[i];
                }

            PROCESS_INFORMATION piProcInfo;
            ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

            auto myproc =
                CreateProcess(NULL, mychararray, NULL, NULL, TRUE, creationFlag, NULL, NULL, &siStartInfo, &piProcInfo);
            CloseHandle(piProcInfo.hProcess);
            CloseHandle(piProcInfo.hThread);
            CloseHandle(g_hChildStd_OUT_Wr);
            CloseHandle(g_hChildStd_IN_Rd);
            start_reading_threads();
            return myproc;
            }

    public:
        bool stdin_write(std::string str) const
            {
            DWORD dwWritten;
            str.append("\n");
            return (bool)WriteFile(g_hChildStd_IN_Wr, str.c_str(), str.size(), &dwWritten, NULL);
            }

    private:
        std::wstring read_from_pipe(HANDLE pipeHandle, std::vector<CHAR>& chBuf) const
            {
            DWORD dwRead;
            chBuf.clear();
            chBuf.resize(buffer_size);
            auto rt{ ReadFile(pipeHandle, chBuf.data(), buffer_size, &dwRead, NULL) };
            std::string tmpstr{ chBuf.begin(), chBuf.begin() + dwRead };
            return s2ws(tmpstr);
            }
        void read_from_stdout()
            {
            std::vector<CHAR> v(buffer_size);
            std::wstring m;
            m.reserve(buffer_size);
            while (continue_reading_stdout)
                {
                m.append(read_from_pipe(g_hChildStd_OUT_Rd, v));
                if (continue_reading_stdout)
                    {
                    strmap_out.emplace_back(ws2s(m));
                    if (print_stdout)
                        {
                        print_yellow(strmap_out.back());
                        }
                    m.clear();
                    if (strmap_out.size() >= stdout_max_len)
                        {
                        strmap_out.erase(strmap_out.begin());
                        }
                    continue;
                    }
                break;
                }
            }
        void read_from_stderr()
            {
            std::vector<CHAR> v(buffer_size);
            std::wstring m;
            m.reserve(buffer_size);
            while (continue_reading_stderr)
                {
                m.append(read_from_pipe(g_hChildStd_ERR_Rd, v));
                if (continue_reading_stderr)
                    {
                    strmap_err.emplace_back(ws2s(m));
                    m.clear();
                    if (print_stderr)
                        {
                        print_red(strmap_err.back());
                        }
                    if (strmap_err.size() >= stderr_max_len)
                        {
                        strmap_err.erase(strmap_err.begin());
                        }
                    continue;
                    }
                break;
                }
            }
        void start_reading_threads()
            {
            t1 = std::thread(&ShellProcessManager::read_from_stdout, this);
            t2 = std::thread(&ShellProcessManager::read_from_stderr, this);
            }

    public:
        std::string get_stdout()
            {
            std::string results;
            results.reserve(4096);
            my_mutex_lock.lock();
            try
                {
                for (auto& pair : strmap_out)
                    {
                    results.append(pair);
                    }
                }
            catch (...)
                {
                }
            strmap_out.clear();
            my_mutex_lock.unlock();
            return results;
            }
        std::string get_stderr()
            {
            std::string results;
            results.reserve(4096);
            my_mutex_lock.lock();
            try
                {
                for (auto& pair : strmap_err)
                    {
                    results.append(pair);
                    }
                }
            catch (...)
                {
                }
            strmap_err.clear();
            my_mutex_lock.unlock();
            return results;
            }
        void clear_stdout()
            {
            my_mutex_lock.lock();
            try
                {
                if (!strmap_out.empty())
                    {
                    strmap_out.clear();
                    }
                }
            catch (...)
                {
                }
            my_mutex_lock.unlock();
            }
        void clear_stderr()
            {
            my_mutex_lock.lock();
            try
                {
                if (!strmap_err.empty())
                    {
                    strmap_err.clear();
                    }
                }
            catch (...)
                {
                }
            my_mutex_lock.unlock();
            }

    private:
        void close_handles() const
            {
            CloseHandle(g_hChildStd_OUT_Rd);
            CloseHandle(g_hChildStd_ERR_Rd);
            CloseHandle(g_hChildStd_IN_Wr);
            }

    public:
        void stop_shell()
            {
            if ((!continue_reading_stdout) && (!continue_reading_stderr))
                {
                return;
                }
            continue_reading_stdout = false;
            continue_reading_stderr = false;
            stdin_write(">&2 echo done stderr\n");
            stdin_write("echo done stdout\n");
            stdin_write(exit_command + "\n" + exit_command + "\n" + exit_command + "\n" + exit_command + "\n" +
                        exit_command);
            Sleep(10);
            close_handles();
            try
                {
                TerminateThread(t1.native_handle(), 1);
                t1.detach();
                t1.join();
                }
            catch (...)
                {
                // std::cout << "" << std::endl;
                }
            try
                {
                TerminateThread(t2.native_handle(), 1);
                t2.detach();
                t2.join();
                }
            catch (...)
                {
                // std::cout << "" << std::endl;
                }
            }
    };
#else

typedef unsigned long DWORD;
typedef int BOOL;
typedef unsigned char BYTE;
typedef unsigned short WORD;
typedef float FLOAT;
typedef FLOAT* PFLOAT;
typedef int INT;
typedef unsigned int UINT;
typedef unsigned int* PUINT;
typedef char* LPSTR;
typedef unsigned char BYTE;
typedef unsigned char* LPBYTE;

class ShellProcessManager
    {
    public:
        ShellProcessManager(std::string shell_command, size_t buffer_size = 4096, size_t stdout_max_len = 4096,
                            size_t stderr_max_len = 4096, std::string exit_command = "exit", int print_stdout = 1,
                            int print_stderr = 1)
            : shell_command(shell_command), continue_reading_stdout(true), continue_reading_stderr(true),
            buffer_size(buffer_size), stdout_max_len(stdout_max_len), stderr_max_len(stderr_max_len),
            exit_command(exit_command), print_stdout((bool)print_stdout), print_stderr((bool)print_stderr)
            {
            }

        ~ShellProcessManager()
            {
            stop_shell();
            }

        bool start_shell(DWORD creationFlag = 0, DWORD creationFlags = 0x08000000, WORD wShowWindow = 1,
                         LPSTR lpReserved = nullptr, LPSTR lpDesktop = nullptr, LPSTR lpTitle = nullptr, DWORD dwX = 0,
                         DWORD dwY = 0, DWORD dwXSize = 0, DWORD dwYSize = 0, DWORD dwXCountChars = 0,
                         DWORD dwYCountChars = 0, DWORD dwFillAttribute = 0, DWORD dwFlags = 0, WORD cbReserved2 = 0,
                         LPBYTE lpReserved2 = nullptr)
            {
            pipe(pip0);
            pipe(pip1);
            pipe(pip2);
            PID = fork();
            if (PID < 0)
                {
                throw std::runtime_error("Failed to fork process");
                }
            if (PID == 0)
                {
                child_process();
                }
            else
                {
                parent_process();
                }
            return true;
            }

        void stdin_write(std::string command)
            {
            std::string mycommand = command + "\n";
            fputs(mycommand.c_str(), pXFile);
            fflush(pXFile);
            }

        std::string get_stdout()
            {
            std::string results;
            results.reserve(4096);
            my_mutex_lock.lock();
            try
                {
                for (auto& pair : strmap_out)
                    {
                    results.append(pair);
                    }
                }
            catch (...)
                {
                }
            strmap_out.clear();
            my_mutex_lock.unlock();
            return results;
            }
        std::string get_stderr()
            {
            std::string results;
            results.reserve(4096);
            my_mutex_lock.lock();
            try
                {
                for (auto& pair : strmap_err)
                    {
                    results.append(pair);
                    }
                }
            catch (...)
                {
                }
            strmap_err.clear();
            my_mutex_lock.unlock();
            return results;
            }

    private:
        std::string shell_command;
        bool continue_reading_stdout;
        bool continue_reading_stderr;
        int pip0[2], pip1[2], pip2[2];
        int FDChildStdin, FDChildStdout, FDChildStderr;
        pid_t PID;
        FILE* pXFile;
        std::vector<std::string> strmap_out;
        std::vector<std::string> strmap_err;
        std::thread t1;
        std::thread t2;
        size_t buffer_size;
        size_t stdout_max_len;
        size_t stderr_max_len;
        std::string exit_command;
        std::mutex my_mutex_lock;
        bool print_stdout;
        bool print_stderr;

        void child_process()
            {
            close(pip0[1]);
            close(pip1[0]);
            close(pip2[0]);
            dup2(pip2[1], 2);
            dup2(pip1[1], 1);
            dup2(pip0[0], 0);
            close(pip0[0]);
            close(pip1[1]);
            close(pip2[1]);
            char* argv[1] = {};
            char* envp[1] = {};
            execve(shell_command.c_str(), argv, envp);
            exit(-1);
            }

        void parent_process()
            {
            FDChildStdin = pip0[1];
            FDChildStdout = pip1[0];
            FDChildStderr = pip2[0];
            pXFile = fdopen(FDChildStdin, "w");

            t1 = std::thread(&ShellProcessManager::read_from_stdout, this);
            t2 = std::thread(&ShellProcessManager::read_from_stderr, this);
            }

        void read_from_stdout()
            {
            std::vector<char> buff;
            buff.resize(buffer_size);
            while (continue_reading_stdout)
                {
                int iret = read(FDChildStdout, buff.data(), buffer_size);
                if (!continue_reading_stdout)
                    break;
                strmap_out.emplace_back(std::string{ buff.begin(), buff.begin() + iret });
                if (print_stdout)
                    {
                    print_yellow(strmap_out.back());
                    }
                if (strmap_out.size() >= stdout_max_len)
                    {
                    strmap_out.erase(strmap_out.begin());
                    }
                buff.clear();
                buff.resize(buffer_size);
                }
            }

        void read_from_stderr()
            {
            std::vector<char> bufferr;
            bufferr.resize(buffer_size);
            while (continue_reading_stderr)
                {
                int iret = read(FDChildStderr, bufferr.data(), buffer_size);
                if (!continue_reading_stderr)
                    break;
                strmap_err.emplace_back(std::string{ bufferr.begin(), bufferr.begin() + iret });
                if (print_stderr)
                    {
                    print_red(strmap_err.back());
                    }
                if (strmap_err.size() >= stderr_max_len)
                    {
                    strmap_err.erase(strmap_err.begin());
                    }
                bufferr.clear();
                bufferr.resize(buffer_size);
                }
            }

    public:
        void stop_shell()
            {
            if (!continue_reading_stdout && !continue_reading_stderr)
                {
                return;
                }
            continue_reading_stdout = false;
            continue_reading_stderr = false;
            stdin_write(">&2 echo done stderr\n");
            stdin_write("echo done stdout\n");
            stdin_write(exit_command + ";" + exit_command + ";" + exit_command + ";" + exit_command + ";" + exit_command);
            fclose(pXFile);
            close(FDChildStdin);
            close(FDChildStdout);
            close(FDChildStderr);
            pthread_cancel(t1.native_handle());
            pthread_cancel(t2.native_handle());
            try
                {
                if (t1.joinable())
                    t1.join();
                }
            catch (...)
                {
                }
            try
                {
                if (t2.joinable())
                    t2.join();
                }
            catch (...)
                {
                };

            }
        void clear_stdout()
            {
            my_mutex_lock.lock();
            try
                {
                if (!strmap_out.empty())
                    {
                    strmap_out.clear();
                    }
                }
            catch (...)
                {
                }
            my_mutex_lock.unlock();
            }
        void clear_stderr()
            {
            my_mutex_lock.lock();
            try
                {
                if (!strmap_err.empty())
                    {
                    strmap_err.clear();
                    }
                }
            catch (...)
                {
                }
            my_mutex_lock.unlock();
            }
    };
#endif
#endif // SHELL_PROCESS_MANAGER_H
