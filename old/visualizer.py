import json
import threading
import asyncio
import websockets
import traceback
import numpy as np
import random
from mmp_math import ModInt

# ==========================================
# 🌟 FIX: ModInt に対するモンキーパッチ
# 計算機内の ModInt が実数(float)と演算された際、
# 勝手に整数に切り捨てて精度を破壊するのを完全に防ぎます。
# ==========================================
_orig_add = ModInt.__add__
_orig_sub = ModInt.__sub__
_orig_mul = ModInt.__mul__
_orig_truediv = ModInt.__truediv__
_orig_rsub = ModInt.__rsub__
_orig_rtruediv = ModInt.__rtruediv__

def _to_float(m):
    # ModInt(有限体)の値を、負の数も考慮して実数空間に復元する
    v = m.value
    return float(v - ModInt.MOD) if v > ModInt.MOD / 2 else float(v)

def _add_patch(self, other):
    if isinstance(other, (float, np.floating)): return _to_float(self) + float(other)
    return _orig_add(self, other)

def _sub_patch(self, other):
    if isinstance(other, (float, np.floating)): return _to_float(self) - float(other)
    return _orig_sub(self, other)

def _rsub_patch(self, other):
    if isinstance(other, (float, np.floating)): return float(other) - _to_float(self)
    return _orig_rsub(self, other)

def _mul_patch(self, other):
    if isinstance(other, (float, np.floating)): return _to_float(self) * float(other)
    return _orig_mul(self, other)

def _div_patch(self, other):
    if isinstance(other, (float, np.floating)): return _to_float(self) / float(other)
    return _orig_truediv(self, other)

def _rdiv_patch(self, other):
    if isinstance(other, (float, np.floating)): return float(other) / _to_float(self)
    return _orig_rtruediv(self, other)

# Pythonの動的特性を活かし、元のクラスの挙動を上書き
ModInt.__add__ = _add_patch
ModInt.__radd__ = _add_patch
ModInt.__sub__ = _sub_patch
ModInt.__rsub__ = _rsub_patch
ModInt.__mul__ = _mul_patch
ModInt.__rmul__ = _mul_patch
ModInt.__truediv__ = _div_patch
ModInt.__rtruediv__ = _rdiv_patch


class RealtimeVisualizer:
    def __init__(self, env):
        self.env = env
        self.clients = set()
        self.static_t_dict = None
        self.loop = None
        threading.Thread(target=self._thread_runner, daemon=True).start()

    def _thread_runner(self):
        try:
            asyncio.run(self._async_server())
        except Exception as e:
            print(f"\n🚨 [Visualizer] サーバー起動エラー: {e}")
            traceback.print_exc()

    async def _async_server(self):
        self.loop = asyncio.get_running_loop()
        print("\n🌐 [Visualizer] WebSocketサーバーを起動中... (ws://127.0.0.1:8765)")
        async with websockets.serve(self._handler, "127.0.0.1", 8765):
            await asyncio.Future()

    async def _handler(self, websocket, path=None):
        self.clients.add(websocket)
        print("🌐 [Visualizer] ブラウザが接続されました！")
        self.broadcast_state()
        try:
            await websocket.wait_closed()
        finally:
            self.clients.remove(websocket)
            print("🌐 [Visualizer] ブラウザが切断されました。")

    def broadcast_state(self, focus_nodes=None, current_theorem=None):
        if not self.clients or self.loop is None: return
        
        if self.static_t_dict is None and getattr(self.env, 'all_vars', None):
            # 🌟 FIX: シードを固定し、-1.5〜1.5の狭く安全な範囲で値を生成する。
            # これにより、どの問題（九点円、シムソン等）でも媒介変数や座標が発散せず綺麗に収まる。
            rng = random.Random(12345)
            self.static_t_dict = {}
            for v in self.env.all_vars:
                val = rng.uniform(-1.5, 1.5)
                # 0に近すぎると退化（点が重なる）するので適度に離す
                if abs(val) < 0.3:
                    val = 0.5 if val >= 0 else -0.5
                self.static_t_dict[v] = float(val)

        state = {
            "nodes": [], 
            "focus": [getattr(n, 'name', str(n)) for n in (focus_nodes or [])],
            "current_theorem": current_theorem or "None"
        }
        cache = {}
        
        seen_reps = set()
        
        for n in self.env.nodes:
            if not getattr(n, 'is_valid', lambda: True)(): continue
            rep = n.get_rep()
            
            # 🌟 FIX: 既にリストに追加済みの同値類(代表元)ならスキップする
            if id(rep) in seen_reps:
                continue
            seen_reps.add(id(rep))
            
            coords = []
            if self.static_t_dict:
                try:
                    coords = rep.calculate(self.static_t_dict, cache)
                except Exception as e:
                    pass 
            
            clean_coords = []
            if coords:
                try:
                    clean_coords = [float(getattr(c, 'value', c)) for c in coords if c is not None]
                except Exception:
                    pass

            parent_names = []
            comp = rep.get_best_component()
            if comp and comp.definitions:
                for p in next(iter(comp.definitions)).parents:
                    if hasattr(p, 'get_rep'):
                        parent_names.append(getattr(p.get_rep(), 'name', '?'))
                    else:
                        parent_names.append(str(p))

            if clean_coords or rep.entity_type in ["Angle", "Scalar", "Direction", "Circle"]:
                state["nodes"].append({
                    "name": getattr(rep, 'name', 'Unknown'),
                    "type": getattr(rep, 'entity_type', 'Unknown'),
                    "heat": getattr(rep, 'heat_bonus', 0.0),
                    "importance": getattr(rep, 'base_importance', 1.0),
                    "coords": clean_coords,
                    "parents": parent_names
                })

        msg = json.dumps(state)
        for ws in list(self.clients):
            try:
                asyncio.run_coroutine_threadsafe(ws.send(msg), self.loop)
            except Exception:
                pass