import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import svgr from "vite-plugin-svgr"
import { nodePolyfills } from 'vite-plugin-node-polyfills'
import importMetaUrlPlugin from '@codingame/esbuild-import-meta-url-plugin'
import { normalizePath } from 'vite'
import path from 'node:path'

const backendPort = process.env.PORT || 8080;
const clientPort = process.env.CLIENT_PORT || 3000;

// https://vitejs.dev/config/
export default defineConfig({
  optimizeDeps: {
    esbuildOptions: {
      plugins: [importMetaUrlPlugin]
    },
    exclude: ['games']
  },
  build: {
    // Relative to the root
    // Note: This has to match the path in `relay/index.mjs` and in `tsconfig.json`
    outDir: 'client/dist',
  },
  plugins: [
    react(),
    svgr({
      // svgr options: https://react-svgr.com/docs/options/
      svgrOptions: { exportType: "default", ref: true, svgo: false, titleProp: true },
       include: "**/*.svg",
    }),
    nodePolyfills({
      overrides: {
        fs: 'memfs',
      },
    }),
    viteStaticCopy({
      targets: [
        {
          src: [
            normalizePath(path.resolve(__dirname, './node_modules/@leanprover/infoview/dist/*')),
            normalizePath(path.resolve(__dirname, './node_modules/lean4monaco/dist/webview/webview.js')),
          ],
          dest: 'infoview'
        },
        {
          src: [
            normalizePath(path.resolve(__dirname, './node_modules/@leanprover/infoview/dist/codicon.ttf'))
          ],
          dest: 'assets'
        }
      ]
    })
  ],
  publicDir: "client/public",
  base: "/", // setting this to `/leanweb/` means the server is now accessible at `localhost:3000/leanweb`
  //root: 'client/src',
  server: {
    port: Number(clientPort),
    proxy: {
      '/websocket': {
        target: `ws://localhost:${backendPort}`,
        ws: true
      },
      '/import': {
        target: `http://localhost:${backendPort}`,
      },
      '/data': {
        target: `http://localhost:${backendPort}`,
      },
      '/i18n': {
        target: `http://localhost:${backendPort}`,
      },
    }
  },
  resolve: {
    alias: {
      path: "path-browserify",
    },
  },
})
